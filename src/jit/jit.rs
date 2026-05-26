use std::{collections::BTreeMap, mem::transmute_copy, rc::Rc};

use crate::{
    jit::{
        analysis::{self, ResolvedSig},
        inline,
    },
    types::{
        self, ArithOp, BasicBlockInstr, CRANELIFT_VALUE, Compiler, FuncMap, Instr, JITFunction,
        MemOp,
    },
};
use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use cranelift::{
    codegen::{
        control::ControlPlane,
        ir::{BlockArg, FuncRef, InstructionData, Opcode, ValueDef},
    },
    frontend::Switch,
    prelude::{
        AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, Signature,
        TrapCode, Value, Variable,
        isa::{CallConv, TargetIsa},
        types::I64,
    },
};

use cranelift_jit::JITModule;
use cranelift_object::object::Import;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use types::Value as ClacValue;

use cranelift_module::{FuncId, Module, ModuleError, ModuleResult};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("Module (cranelift) Error: {0}")]
    ModuleError(#[from] ModuleError),

    #[error("JIT Compilation Error: {0}")]
    JITError(#[from] JITError),
}

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

const CLAC_VALUE_STRIDE: i64 = size_of::<ClacValue>() as i64;
const ALIGNED: MemFlags = MemFlags::new().with_aligned();

fn emit_pop_loadless(bu: &mut FunctionBuilder, stack: Variable) -> Value {
    let pos = bu.use_var(stack);
    let new_pos = bu.ins().iadd_imm(pos, -CLAC_VALUE_STRIDE);
    bu.def_var(stack, new_pos);

    new_pos
}

fn emit_push(bu: &mut FunctionBuilder, stack: Variable, val: Value) {
    let pos = bu.use_var(stack);

    bu.ins().store(ALIGNED, val, pos, 0);

    let new_pos = bu.ins().iadd_imm(pos, CLAC_VALUE_STRIDE);
    bu.def_var(stack, new_pos);
}

fn emit_pop(bu: &mut FunctionBuilder, stack: Variable) -> Value {
    let new_pos = emit_pop_loadless(bu, stack);

    bu.ins().load(CRANELIFT_VALUE, ALIGNED, new_pos, 0)
}

fn emit_pick(bu: &mut FunctionBuilder, stack: Variable, offset: Value) {
    let rsp = bu.use_var(stack);

    // let offset_minus_1 = bu.ins().isub(offset, bu.ins().iconst(CRANELIFT_VALUE, 1));

    // let negative = bu.ins().icmp_imm(Cond, x, Y)
    let offset_multiplied = bu.ins().imul_imm(offset, CLAC_VALUE_STRIDE);
    let target_pos = bu.ins().isub(rsp, offset_multiplied);
    let loaded = bu.ins().load(CRANELIFT_VALUE, ALIGNED, target_pos, 0);
    emit_push(bu, stack, loaded);
}

fn compile_block(
    idx: usize,
    blocks: &BTreeMap<usize, UnifiedBlock>,
    stack: Option<Variable>, // whether this exists will be used to determine whether we flush or not
    bu: &mut FunctionBuilder,
    isa: &dyn TargetIsa,
    refs: &ImportRefs,
    (trap_block, term_block): (cranelift::prelude::Block, cranelift::prelude::Block),
    block_param_counts: &mut HashMap<usize, usize>,
    this_is_a_noreturn_function: bool,
) {
    let UnifiedBlock { code, cranelift }: &UnifiedBlock = blocks.get(&idx).unwrap();

    let cb = *cranelift;
    bu.switch_to_block(cb);
    bu.seal_block(cb);

    if stack.is_none() {
        let Some(&paramc) = block_param_counts.get(&idx) else {
            println!("[!] Block {idx}: {code:?} skipped because it is not reachable!");
            return;
        };

        for _ in 0..paramc {
            bu.append_block_param(cb, CRANELIFT_VALUE);
        }
    }

    // Idea:
    // 2 levels of stack
    // there is the REAL stack (passed in pointer)
    // and also a build/function stack (*mut ClacStack)
    //
    // Before if statements/control flow, we commit/flush the build function stack, which means pushing everything onto the build function stack onto the real stack.
    // if we get to the final block, then we geneate instructions to push all of the build stack onto the REAL stack.
    // must also flush before Pick
    //
    // every function is fn(*mut ClacStack) -> *mut ClacStack
    let mut tmp: Vec<Value> = match stack {
        None => Vec::from(bu.block_params(cb)),
        Some(_) => {
            match idx {
                0 => assert_eq!(bu.block_params(cb).len(), 1),
                _ => assert_eq!(bu.block_params(cb).len(), 0),
            }

            Vec::new()
        }
    };

    dbg_println!(
        "compiling block = {:?} | initial tmp = {:?} | block param counts = {block_param_counts:?}",
        code,
        tmp
    );

    let flush: Box<dyn Fn(&mut Vec<Value>, &mut FunctionBuilder) -> Vec<Value>> = match stack {
        None => Box::new(|tmp, bu| std::mem::take(tmp)),
        Some(stack) => Box::new(move |tmp, bu| {
            let tmp = std::mem::take(tmp);

            for val in tmp.into_iter() {
                emit_push(bu, stack, val);
            }

            vec![bu.use_var(stack)]
        }),
    };

    let xpop: Box<dyn Fn(&mut Vec<Value>, &mut FunctionBuilder) -> Value> = match stack {
        None => Box::new(|tmp, bu| {
            tmp.pop()
                .expect("By Clacanalysis reach calculation, this should hold")
        }),
        Some(stack) => Box::new(move |tmp, bu| tmp.pop().unwrap_or_else(|| emit_pop(bu, stack))),
    };

    let xpop_no_value: Box<dyn Fn(&mut Vec<Value>, &mut FunctionBuilder)> = match stack {
        None => Box::new(|tmp, bu| {
            tmp.pop()
                .expect("By Clacanalysis reach calculation, this should hold");
        }),
        Some(stack) => Box::new(move |tmp, bu| {
            tmp.pop().unwrap_or_else(|| emit_pop_loadless(bu, stack));
        }),
    };

    // let value_to_const =
    //     |func: &cranelift::codegen::ir::Function, val: Value| -> Option<ClacValue> {
    //         let valuedef = func.dfg.value_def(val);

    //         let ValueDef::Result(inst, 0) = valuedef else {
    //             return None;
    //         };

    //         let res = func.dfg.insts[inst];
    //         let InstructionData::UnaryImm {
    //             opcode: Opcode::Iconst,
    //             imm: num,
    //         } = res
    //         else {
    //             return None;
    //         };
    //         Some(num.into())
    //     };

    let line = &code.code;

    for (i, inst) in line.iter().enumerate() {
        match inst {
            BasicBlockInstr::Literal(n) => {
                let out = bu.ins().iconst(I64, *n);
                tmp.push(out);
            }
            BasicBlockInstr::Arith(it) => {
                let b = xpop(&mut tmp, bu);
                let a = xpop(&mut tmp, bu);

                tmp.push(match it {
                    ArithOp::Add => bu.ins().iadd(a, b),
                    ArithOp::Sub => bu.ins().isub(a, b),
                    ArithOp::Mul => bu.ins().imul(a, b),
                    ArithOp::Div => bu.ins().sdiv(a, b),
                    ArithOp::Rem => bu.ins().srem(a, b),
                    ArithOp::Lt => {
                        let cmp = bu.ins().icmp(IntCC::SignedLessThan, a, b);
                        bu.ins().sextend(CRANELIFT_VALUE, cmp)
                    }
                    ArithOp::Pow => {
                        let call = bu.ins().call(refs.builtins.powfunc, &[a, b]);
                        bu.inst_results(call)[0]
                    }
                });
            }
            BasicBlockInstr::Swap => {
                let b = xpop(&mut tmp, bu);
                let a = xpop(&mut tmp, bu);

                tmp.push(b);
                tmp.push(a);
            }
            BasicBlockInstr::Rot => {
                let z = xpop(&mut tmp, bu);
                let y = xpop(&mut tmp, bu);
                let x = xpop(&mut tmp, bu);

                tmp.push(y);
                tmp.push(z);
                tmp.push(x);
            }
            BasicBlockInstr::Drop => {
                xpop_no_value(&mut tmp, bu);
            }
            BasicBlockInstr::Print => {
                let popped = xpop(&mut tmp, bu);
                bu.ins().call(refs.builtins.printfunc, &[popped]);
            }
            BasicBlockInstr::Quit => {
                // TODO: this should be a terminator/no return
                bu.ins().call(refs.builtins.quitfunc, &[]);
            }
            &BasicBlockInstr::ResolvedPick(n) => {
                // assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), n);
                // let n: usize = n.try_into().unwrap();

                // TODO: turn this into trap otherwise
                assert!(n > 0);

                if n <= tmp.len() {
                    tmp.push(tmp[tmp.len() - n]);
                } else {
                    let stack =
                        stack.expect("This case should not occur if Clacanalysis worked correctly");

                    let amt: i64 = (n - tmp.len()).try_into().unwrap();
                    assert!(amt > 0);

                    let x: i32 = (-amt * CLAC_VALUE_STRIDE).try_into().unwrap();

                    let rsp = bu.use_var(stack);
                    let loaded = bu.ins().load(CRANELIFT_VALUE, ALIGNED, rsp, x);
                    tmp.push(loaded);
                }
            }
            BasicBlockInstr::BadPick => {
                let stack = stack.expect("This must be a not well-behaved function");

                let popped = xpop(&mut tmp, bu);

                // TODO: improve
                flush(&mut tmp, bu);

                emit_pick(bu, stack, popped);
            }
            BasicBlockInstr::FunctionCall(func) => {
                let Some((callee_ref, callee_sig)) = refs.clac.0.get(func.as_str()) else {
                    dbg_println!("TRYING TO CALL UNRESOLVED FUNCTION: {func:?}");
                    bu.ins().trap(TrapCode::unwrap_user(67));
                    return;
                };

                let args: Vec<_> = match callee_sig {
                    Some(callee_sig) => {
                        let argc = callee_sig.argc();

                        let mut out: Vec<_> = (0..argc).map(|_| xpop(&mut tmp, bu)).collect();
                        out.reverse();
                        out
                    }
                    None => {
                        let stack = stack.expect(
                            "A well behaved function cannot call non-well-behaved functions",
                        );

                        flush(&mut tmp, bu)
                    }
                };

                // TAIL CALL OPTIMIZATION
                let tailcall_candidate = match (stack, callee_sig) {
                    // Well CALLS well OK only when tmp.len() == 0
                    (None, Some(_)) if tmp.len() == 0 => true,

                    // Bad Calls Bad OK
                    (Some(_), None) => true,

                    // Bad Calls Well -- Won't work
                    // Well Calls Bad -- IMPOSSIBLE
                    _ => false,
                };

                if tailcall_candidate
                    && i == line.len() - 1
                    && let analysis::Terminator::Jump(analysis::Next::Terminate) = code.terminator
                {
                    assert_eq!(tmp.len(), 0);

                    bu.ins().return_call(*callee_ref, &args);
                    return;
                }

                let ret = bu.ins().call(*callee_ref, &args);
                match callee_sig {
                    Some(_) => {
                        tmp.extend(bu.inst_results(ret));
                    }
                    None => {
                        let stack = stack.expect(
                            "A well behaved function cannot call non-well-behaved functions",
                        );

                        // update stack
                        let ret = bu.inst_results(ret)[0];
                        bu.def_var(stack, ret);
                    }
                }
            }
            BasicBlockInstr::Mem(memop) => {
                match memop {
                    MemOp::Read8 => {
                        let addr = xpop(&mut tmp, bu);

                        tmp.push(bu.ins().uload8(CRANELIFT_VALUE, MemFlags::new(), addr, 0));
                    }

                    MemOp::Write8 => {
                        let value /*: u8*/ = xpop(&mut tmp, bu);
                        let addr = xpop(&mut tmp, bu);

                        // TODO: this will DISCARD BITS
                        bu.ins().istore8(MemFlags::new(), value, addr, 0);
                    }

                    MemOp::ReadNative => {
                        let addr = xpop(&mut tmp, bu);
                        tmp.push(bu.ins().load(CRANELIFT_VALUE, MemFlags::new(), addr, 0));
                    }

                    MemOp::WriteNative => {
                        let value = xpop(&mut tmp, bu);
                        let addr = xpop(&mut tmp, bu);

                        bu.ins().store(MemFlags::new(), value, addr, 0);
                    }

                    MemOp::WidthNative => {
                        let amt: i64 = ClacValue::BITS.into();
                        tmp.push(bu.ins().iconst(CRANELIFT_VALUE, amt));
                    }
                };
            }
            // TODO: optimize by special casing on compile time known ranges
            &BasicBlockInstr::ResolvedDropRange { start, amt } => {
                // assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), amount);

                // assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), start);

                // bu.emit_small_memory_copy( config, dest, src, size, dest_align, src_align, non_overlapping, flags, );

                assert!(amt >= 0);
                // TODO: make this a trap instead
                // test case: 1 2 3 4 5   3 5 drop_range
                assert!(start >= amt);

                let keep: usize = (start - amt).try_into().unwrap();
                let mut out = Vec::with_capacity(keep);

                for _ in 0..keep {
                    out.push(xpop(&mut tmp, bu));
                }

                for _ in 0..amt {
                    xpop_no_value(&mut tmp, bu);
                }

                for x in out.into_iter().rev() {
                    tmp.push(x);
                }
            }
            BasicBlockInstr::BadDropRange => {
                let amount = xpop(&mut tmp, bu);
                let start = xpop(&mut tmp, bu);

                let value_sz: i64 = CLAC_VALUE_STRIDE.try_into().unwrap();

                let start_strided = bu.ins().imul_imm(start, value_sz);
                let amount_strided = bu.ins().imul_imm(amount, value_sz);

                // TODO: undefined behavior (?)
                // let true = amount <= start else {
                //     return Err(ExecError::InvalidDropRange);
                // };

                // TODO: maybe can remove flush?
                // flush(&mut tmp, bu);
                let stack = stack.expect("this should be a bad (not well-behaved) function");
                let rsp = flush(&mut tmp, bu)[0];

                let drop_start = bu.ins().isub(rsp, start_strided);
                let drop_end = bu.ins().iadd(drop_start, amount_strided);

                // TODO: undefined behavior
                // debug_assert!(stack.rsp >= drop_end);

                let keep_amount = bu.ins().isub(start, amount);
                let keep_amount_strided = bu.ins().imul_imm(keep_amount, value_sz);
                // TODO: assert that keep_amount >= 0

                bu.call_memmove(
                    isa.frontend_config(),
                    drop_start,
                    drop_end,
                    keep_amount_strided,
                );

                let new_rsp = bu.ins().isub(rsp, amount_strided);
                bu.def_var(stack, new_rsp);
            }
            BasicBlockInstr::Syscall => {
                let v6 = xpop(&mut tmp, bu);
                let v5 = xpop(&mut tmp, bu);
                let v4 = xpop(&mut tmp, bu);
                let v3 = xpop(&mut tmp, bu);
                let v2 = xpop(&mut tmp, bu);
                let v1 = xpop(&mut tmp, bu);
                let rax = xpop(&mut tmp, bu);

                let sysc = bu
                    .ins()
                    .call(refs.builtins.syscall, &[rax, v1, v2, v3, v4, v5, v6]);

                tmp.push(bu.inst_results(sysc)[0]);
            }
        }
    }

    let cache_param_count = |bpc: &mut HashMap<usize, usize>, block: usize, count: usize| {
        bpc.entry(block)
            .and_modify(|old| assert_eq!(*old, count))
            .or_insert(count);
    };

    // build terminator
    // let mut build_return = |bu: &mut FunctionBuilder, next: &analysis::Next| ;

    let mut get_block_and_args =
        |next: &analysis::Next, bu: &mut FunctionBuilder, args: &[BlockArg]| {
            match next {
                analysis::Next::Trap => (trap_block, vec![]), // TODO: fix
                analysis::Next::Terminate => (term_block, Vec::from(args)),
                analysis::Next::Block(block) => {
                    cache_param_count(block_param_counts, *block, args.len());
                    (
                        blocks[block].cranelift,
                        if stack.is_none() {
                            Vec::from(args)
                        } else {
                            vec![]
                        },
                    )
                }
            }
        };

    match &code.terminator {
        analysis::Terminator::Jump(next) => {
            match next {
                analysis::Next::Trap => {
                    bu.ins().trap(TrapCode::unwrap_user(67));
                }
                analysis::Next::Terminate => {
                    let out = &flush(&mut tmp, bu);
                    if this_is_a_noreturn_function {
                        bu.ins().trap(TrapCode::unwrap_user(68));
                    } else {
                        bu.ins().return_(out);
                    }
                }
                analysis::Next::Block(block) => {
                    let cranelifted = blocks[block].cranelift;

                    let out: Vec<_> = flush(&mut tmp, bu)
                        .into_iter()
                        .map(|x| BlockArg::Value(x))
                        .collect();

                    cache_param_count(block_param_counts, *block, out.len());

                    // TODO: this may add extraneous block arguments
                    bu.ins().jump(
                        cranelifted,
                        if stack.is_none() { out.as_slice() } else { &[] },
                    );
                }
            }
        }
        analysis::Terminator::If { on_true, on_false } => {
            let cond = xpop(&mut tmp, bu);

            let out: Vec<_> = flush(&mut tmp, bu)
                .into_iter()
                .map(|x| BlockArg::Value(x))
                .collect();

            let (on_true, on_true_args) = get_block_and_args(on_true, bu, &out);
            let (on_false, on_false_args) = get_block_and_args(on_false, bu, &out);

            bu.ins()
                .brif(cond, on_true, &on_true_args, on_false, &on_false_args);
        }
        analysis::Terminator::Skip { targets } => {
            let mut switch = Switch::new();

            let popped = xpop(&mut tmp, bu);

            let out: Vec<_> = flush(&mut tmp, bu)
                .into_iter()
                .map(|x| BlockArg::Value(x))
                .collect();

            let targets: Vec<_> = targets
                .into_iter()
                .map(|nx| (get_block_and_args(nx, bu, &out), bu.create_block()))
                .collect();

            for (i, (_, trampoline)) in targets.iter().enumerate() {
                switch.set_entry(i as u128, *trampoline);
            }
            switch.emit(bu, popped, trap_block);

            // seal trampolines
            targets
                .into_iter()
                .for_each(|((real_block, args), trampoline)| {
                    bu.switch_to_block(trampoline);
                    bu.ins().jump(real_block, &args);
                    bu.seal_block(trampoline);
                });
        }
    }
}

#[derive(Debug)]
pub(crate) struct BuiltinRefs {
    printfunc: FuncRef,
    quitfunc: FuncRef,
    powfunc: FuncRef,
    syscall: FuncRef,
}

#[derive(Debug, Error)]
pub enum JITError {
    #[error("Indeterminate Control Flow")]
    IndeterminateControlFlow,

    #[error("Detected a negative skip!")]
    BadSkip,
}

fn generate_clac_function_signature(isa: &dyn TargetIsa, callconv: CallConv) -> Signature {
    let ptr_t = isa.pointer_type();
    let ptr_arg = AbiParam::new(ptr_t);

    Signature {
        params: vec![ptr_arg],  // *mut ClacValue
        returns: vec![ptr_arg], // *mut ClacValue
        call_conv: callconv,
    }
}

pub(crate) fn get_function(module: &JITModule, func: FuncId) -> JITFunction {
    unsafe { transmute_copy(&module.get_finalized_function(func)) }
}

#[derive(Debug)]
pub(crate) struct Callees<'names, 'sigs>(
    HashMap<&'names str, (FuncRef, Option<&'sigs analysis::ResolvedSig>)>,
);

#[derive(Debug)]
pub struct ImportRefs<'names, 'sigs> {
    clac: Callees<'names, 'sigs>,
    builtins: BuiltinRefs,
}

fn get_callees(line: &[types::Instr]) -> HashSet<&str> {
    line.iter()
        .filter_map(|x| {
            let Instr::BBInstr(BasicBlockInstr::FunctionCall(funcref)) = x else {
                return None;
            };

            Some(funcref.as_str())
        })
        .collect()
}

struct UnifiedBlock {
    code: analysis::Block,
    cranelift: cranelift::prelude::Block,
}

impl<T: Module> Compiler<T> {
    pub(crate) fn generate_signature(&self, callconv: CallConv) -> Signature {
        generate_clac_function_signature(self.module.isa(), callconv)
    }

    fn declare_callees(
        &mut self,
        func: &mut cranelift::codegen::ir::Function,
        callees: impl Iterator<Item = FuncId>,
    ) -> HashMap<FuncId, FuncRef> {
        let mut ret = HashMap::new();

        for id in callees {
            ret.insert(id, self.module.declare_func_in_func(id, func));
        }

        ret
    }

    pub(crate) fn define_wrapper(
        &mut self,
        name: &str,
        to_wrap: FuncId,
        target_sig: Option<&ResolvedSig>,
        ctx: &mut cranelift::codegen::Context,
        fbctx: &mut FunctionBuilderContext,
    ) -> ModuleResult<FuncId> {
        let sig = self.generate_signature(self.module.isa().default_call_conv());

        let wrapper_id =
            self.module
                .declare_function(name, cranelift_module::Linkage::Export, &sig)?;

        self.module.clear_context(ctx);
        ctx.func.signature = sig;

        let target = self.module.declare_func_in_func(to_wrap, &mut ctx.func);

        let mut bu = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = bu.create_block();
        bu.switch_to_block(entry);
        bu.seal_block(entry);

        bu.append_block_params_for_function_params(entry);

        let stack = bu.block_params(entry)[0];

        match target_sig {
            None => {
                let ret = bu.ins().call(target, &[stack]);
                let ret: Vec<_> = Vec::from(bu.inst_results(ret));

                bu.ins().return_(&ret);
            }
            Some(target_sig) => {
                let argc = target_sig.argc();

                let stack_var = bu.declare_var(self.module.isa().pointer_type());
                bu.def_var(stack_var, stack);

                let mut args: Vec<_> = (0..argc).map(|_| emit_pop(&mut bu, stack_var)).collect();
                args.reverse();

                let ret = bu.ins().call(target, &args);
                let ret = Vec::from(bu.inst_results(ret));

                ret.into_iter()
                    .for_each(|x| emit_push(&mut bu, stack_var, x));

                let final_stack_var = bu.use_var(stack_var);
                bu.ins().return_(&[final_stack_var]);
            }
        }

        bu.finalize();

        self.module.define_function(wrapper_id, ctx)?;

        Ok(wrapper_id)
    }

    pub fn compile_function(
        (function, signature): (BTreeMap<usize, analysis::Block>, Option<&ResolvedSig>),
        mut ctx: cranelift::codegen::Context,
        import_refs: ImportRefs,
        isa: &dyn TargetIsa,
    ) -> Result<cranelift::codegen::Context, CompilerError> {
        if cfg!(feature = "debug") {
            ctx.set_disasm(true);
        }

        let mut fbctx = FunctionBuilderContext::new();

        // TODO: fix when better function analysis is added
        ctx.func.signature = signature.map_or_else(
            || generate_clac_function_signature(isa, CallConv::Tail),
            |x| x.to_cranelift_signature(CallConv::Tail),
        );

        let mut bu = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        let function: BTreeMap<_, _> = function
            .into_iter()
            .map(|(pos, block)| {
                (
                    pos,
                    UnifiedBlock {
                        code: block,
                        cranelift: bu.create_block(),
                    },
                )
            })
            .collect();

        let Some(entry) = function.get(&0) else {
            // create identity block
            let x = bu.create_block();

            bu.switch_to_block(x);
            bu.append_block_params_for_function_params(x);

            bu.seal_block(x);

            let block_params = Vec::from(bu.block_params(x));
            bu.ins().return_(&block_params);

            bu.finalize();

            dbg_println!("compiled empty function");

            return Ok(ctx);
        };

        // dbg_println!("entry = {:?}", entry);

        let entry_block = entry.cranelift;

        bu.append_block_params_for_function_params(entry_block);
        bu.switch_to_block(entry_block);

        // TODO: there should be a better way of ensuring that entry is actually the entry
        bu.func.layout.append_block(entry_block);

        let stack = match signature {
            None => {
                let entry_block_params = bu.block_params(entry_block);
                assert_eq!(entry_block_params.len(), 1);

                let stack = bu.block_params(entry_block)[0];
                let stack_var = bu.declare_var(isa.pointer_type());
                bu.def_var(stack_var, stack);

                Some(stack_var)
            }
            Some(_) => None,
        };

        let trap_block = bu.create_block();
        let term_block = bu.create_block();

        let retc = signature.map_or(1, |x| x.retc());

        for _ in 0..retc {
            bu.append_block_param(term_block, CRANELIFT_VALUE);
        }

        let mut block_param_counts: HashMap<usize, usize> = HashMap::new();
        // NOTE: since we do append block params for func params, we don't need to do any additional appends for the entry block
        block_param_counts.insert(0, 0);

        // is never type
        let is_noreturn = match signature {
            Some(sig) => match sig.delta {
                None => true,
                Some(_) => false,
            },
            None => false,
        };

        for (idx, _) in function.iter() {
            compile_block(
                *idx,
                &function,
                stack,
                &mut bu,
                isa,
                &import_refs,
                (trap_block, term_block),
                &mut block_param_counts,
                is_noreturn,
            );
        }

        bu.seal_block(trap_block);
        bu.seal_block(term_block);

        // build trap block
        bu.switch_to_block(trap_block);
        bu.ins().trap(TrapCode::unwrap_user(67));

        // build term block
        bu.switch_to_block(term_block);
        let params = Vec::from(bu.block_params(term_block));
        bu.ins().return_(&params);

        println!("ctx func display: {}", bu.func.display());

        bu.finalize();

        ctx.inline(inline::ClacInliner {});

        Ok(ctx)
    }
}

impl<T: Module> Compiler<T> {
    pub(crate) fn compile(
        mut self,
        funcs: &types::FuncMap,
    ) -> Result<(T, HashMap<String, FuncId>), CompilerError> {
        let types::Imports {
            printfunc,
            quitfunc,
            powfunc,
            syscallfunc,
        } = self.imports;

        let mut graph: petgraph::Graph<&str, ()> = petgraph::Graph::new();

        // add nodes to graph
        let nodes: HashMap<_, _> = funcs
            .iter()
            .map(|(name, _)| (name.as_str(), graph.add_node(name.as_str())))
            .collect();

        // get callees from all fucntions
        // Only consists of Valid callees (callees that exist)
        let callee_map: HashMap<_, Vec<_>> = funcs
            .iter()
            .map(|(name, code)| {
                (
                    name.as_str(),
                    get_callees(code)
                        .into_iter()
                        .filter(|callee| funcs.contains_key(*callee))
                        .collect(),
                )
            })
            .collect();

        // add edges
        callee_map
            .iter()
            .flat_map(|(&name, callees)| callees.iter().map(move |callee| (name, callee)))
            .map(|(caller, callee)| (nodes[callee], nodes[caller], ()))
            .for_each(|(a, b, c)| {
                graph.add_edge(a, b, c);
            });

        let graph = petgraph::algo::condensation(graph, true);

        // TODO: fix this
        let funcs2 = funcs
            .iter()
            .map(|(a, b)| (a.as_str(), b.as_slice()))
            .collect();

        let analysis::AnalysisResult {
            code: mut function_cfgs,
            resolved_sigs,
        } = analysis::analyze(&graph, &funcs2);

        // let x = petgraph::dot::Dot::with_config(&graph, &[]);
        // let out = format!("{:?}", x);
        // let mut file = std::fs::File::create("graph.dot").unwrap();
        // file.write_all(out.as_bytes()).unwrap();

        // assign cranelift FuncIDs
        let declared: HashMap<&str, FuncId> = funcs
            .iter()
            .map(|(name, _)| {
                let sig = resolved_sigs.get(name.as_str()).map_or_else(
                    || self.generate_signature(CallConv::Tail),
                    |x| x.to_cranelift_signature(CallConv::Tail),
                );

                (
                    name.as_str(),
                    self.module.declare_anonymous_function(&sig).unwrap(),
                )
            })
            .collect();

        let combined_map: HashMap<&str, _> = callee_map
            .into_iter()
            .map(|(name, callees)| {
                let mut ctx = self.module.make_context();

                let callees = callees
                    .into_iter()
                    .map(|callee| {
                        (
                            callee,
                            (
                                self.module.declare_func_in_func(
                                    *declared
                                        .get(callee)
                                        .expect("callees should only have valid callees"),
                                    &mut ctx.func,
                                ),
                                resolved_sigs.get(callee),
                            ),
                        )
                    })
                    .collect();

                let builtins = BuiltinRefs {
                    printfunc: self.module.declare_func_in_func(printfunc, &mut ctx.func),
                    quitfunc: self.module.declare_func_in_func(quitfunc, &mut ctx.func),
                    powfunc: self.module.declare_func_in_func(powfunc, &mut ctx.func),
                    syscall: self.module.declare_func_in_func(syscallfunc, &mut ctx.func),
                };

                (
                    name,
                    (
                        ImportRefs {
                            clac: Callees(callees),
                            builtins,
                        },
                        ctx,
                        function_cfgs.remove(name).unwrap(),
                    ),
                )
            })
            .collect();

        assert_eq!(function_cfgs.len(), 0);

        let isa = self.module.isa();

        let res: HashMap<_, _> = combined_map
            .into_iter()
            .map(|(func_name, (import_refs, ctx, cfg))| {
                let mut translated = Self::compile_function(
                    (cfg, resolved_sigs.get(func_name)),
                    ctx,
                    import_refs,
                    isa,
                )
                .unwrap();

                translated
                    .compile(isa, &mut ControlPlane::default())
                    .unwrap();

                (func_name, translated)
            })
            .collect();

        for (name, ctx) in res {
            // TODO: We have to do this because module.define_function re-compiles the Context for some reason. Currently cranelift does not seem to have an API to do this. (defining a function from a context without re-compiling)
            let buffer = &ctx.compiled_code().unwrap().buffer;
            let func_id = *declared.get(name).unwrap();

            let relocs: Vec<_> = buffer
                .relocs()
                .iter()
                .map(|reloc| {
                    cranelift_module::ModuleReloc::from_mach_reloc(&reloc, &ctx.func, func_id)
                })
                .collect();

            self.module.define_function_bytes(
                func_id,
                buffer.alignment as u64,
                buffer.data(),
                relocs.as_slice(),
            )?;

            dbg_println!("{name} IR: {}", ctx.func.display());

            dbg_println!(
                "Disassembly of {name}: {}",
                ctx.compiled_code().unwrap().vcode.as_ref().unwrap()
            );
        }

        let mut ctx = self.module.make_context();
        let mut fbctx = FunctionBuilderContext::new();

        let out = declared
            .into_iter()
            .map(|(name, id)| {
                (
                    name.to_string(),
                    self.define_wrapper(name, id, resolved_sigs.get(name), &mut ctx, &mut fbctx)
                        .unwrap(),
                )
            })
            .collect();

        Ok((self.module, out))
    }
}
