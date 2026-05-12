use std::{mem::transmute_copy, rc::Rc};

use crate::{
    jit::analysis::{
        self, function_results_from_following_jump_path_to_return_unless_side_effect_found,
    },
    types::{self, ArithOp, CRANELIFT_VALUE, Compiler, Instr, JITFunction, MemOp},
};
use ahash::{HashMap, HashMapExt};
use cranelift::{
    codegen::{
        cursor::{Cursor, CursorPosition, FuncCursor},
        ir::{FuncRef, InstructionData, Opcode, ValueDef},
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
    block: Rc<analysis::Block>,
    stack: Variable,
    bu: &mut FunctionBuilder,
    isa: &dyn TargetIsa,
    (funcs, calleemap): (&HashMap<&str, FuncId>, &HashMap<FuncId, FuncRef>),
    (trap_block, term_block): (cranelift::prelude::Block, cranelift::prelude::Block),
    refs: &ImportRefs,
) {
    // dbg_println!("compiling block = {:?}", block);

    let cb = block.cranelift_block;
    bu.switch_to_block(cb);
    bu.seal_block(cb);

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
    let mut tmp: Vec<Value> = Vec::new();

    let flush = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
        for val in &*tmp {
            emit_push(bu, stack, *val);
        }

        tmp.clear();
    };

    let xpop = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
        tmp.pop().unwrap_or_else(|| emit_pop(bu, stack))
    };

    let xpop_no_value = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
        tmp.pop().unwrap_or_else(|| emit_pop_loadless(bu, stack))
    };

    let value_to_const =
        |func: &cranelift::codegen::ir::Function, val: Value| -> Option<ClacValue> {
            let valuedef = func.dfg.value_def(val);

            let ValueDef::Result(inst, 0) = valuedef else {
                return None;
            };

            let res = func.dfg.insts[inst];
            let InstructionData::UnaryImm {
                opcode: Opcode::Iconst,
                imm: num,
            } = res
            else {
                return None;
            };
            Some(num.into())
        };

    let line = block.code.0;

    for (i, inst) in line.iter().enumerate() {
        use types::Instr;

        match inst {
            Instr::Literal(n) => {
                let out = bu.ins().iconst(I64, *n);
                tmp.push(out);
            }
            Instr::Arith(it) => {
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
                        let call = bu.ins().call(refs.powfunc, &[a, b]);
                        bu.inst_results(call)[0]
                    }
                });
            }
            Instr::Swap => {
                let b = xpop(&mut tmp, bu);
                let a = xpop(&mut tmp, bu);

                tmp.push(b);
                tmp.push(a);
            }
            Instr::Rot => {
                let z = xpop(&mut tmp, bu);
                let y = xpop(&mut tmp, bu);
                let x = xpop(&mut tmp, bu);

                tmp.push(y);
                tmp.push(z);
                tmp.push(x);
            }
            Instr::Drop => {
                xpop_no_value(&mut tmp, bu);
            }
            Instr::Print => {
                let popped = xpop(&mut tmp, bu);
                bu.ins().call(refs.printfunc, &[popped]);
            }
            Instr::Quit => {
                bu.ins().call(refs.quitfunc, &[]);
            }
            Instr::Pick
                if i > 0
                    && let Some(&Instr::Literal(n)) = line.get(i - 1) =>
            {
                assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), n);

                let n: usize = n.try_into().unwrap();

                // TODO: improve
                if n <= tmp.len() {
                    tmp.push(tmp[tmp.len() - n]);
                } else {
                    let amt: i64 = (n - tmp.len()).try_into().unwrap();
                    assert!(amt > 0);

                    let x: i32 = (-amt * CLAC_VALUE_STRIDE).try_into().unwrap();

                    let rsp = bu.use_var(stack);
                    let loaded = bu.ins().load(CRANELIFT_VALUE, ALIGNED, rsp, x);
                    tmp.push(loaded);
                }
            }
            Instr::Pick => {
                let popped = xpop(&mut tmp, bu);

                // TODO: improve
                flush(&mut tmp, bu);

                emit_pick(bu, stack, popped);
            }
            Instr::If | Instr::Skip => {
                unreachable!("There should not be any control flow in this code")
            }
            Instr::FunctionCall(func) => {
                let Some(func) = funcs.get(func.0.as_str()) else {
                    dbg_println!("TRYING TO CALL UNRESOLVED FUNCTION: {func:?}");
                    bu.ins().trap(TrapCode::unwrap_user(67));
                    return;
                };

                let func = calleemap[func];

                flush(&mut tmp, bu);
                let final_stack = bu.use_var(stack);

                // if i == line.len() - 1 && is_last_block {
                //     bu.ins().return_call(*func, &[final_stack]);
                //     return;
                // }

                // TAIL CALL OPTIMIZATION
                if i == line.len() - 1
                    && let analysis::Terminator::Jump(analysis::Next::Terminate) = block.terminator
                {
                    bu.ins().return_call(func, &[final_stack]);
                    return;
                }

                let ret = bu.ins().call(func, &[final_stack]);
                // update stack
                let ret = bu.inst_results(ret)[0];
                bu.def_var(stack, ret);
            }
            Instr::Mem(memop) => {
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
            Instr::DropRange
                if i >= 2
                    && let &[Instr::Literal(start), Instr::Literal(amount)] = &line[i - 2..i] =>
            {
                assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), amount);

                assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), start);

                // bu.emit_small_memory_copy( config, dest, src, size, dest_align, src_align, non_overlapping, flags, );

                assert!(amount >= 0);
                assert!(start >= amount);

                let keep: usize = (start - amount).try_into().unwrap();
                let mut out = Vec::with_capacity(keep);

                for _ in 0..keep {
                    out.push(xpop(&mut tmp, bu));
                }

                for _ in 0..amount {
                    xpop_no_value(&mut tmp, bu);
                }

                for x in out.into_iter().rev() {
                    tmp.push(x);
                }
            }
            Instr::DropRange => {
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
                flush(&mut tmp, bu);

                let rsp = bu.use_var(stack);

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
            Instr::Syscall => {
                let v6 = xpop(&mut tmp, bu);
                let v5 = xpop(&mut tmp, bu);
                let v4 = xpop(&mut tmp, bu);
                let v3 = xpop(&mut tmp, bu);
                let v2 = xpop(&mut tmp, bu);
                let v1 = xpop(&mut tmp, bu);
                let rax = xpop(&mut tmp, bu);

                let sysc = bu.ins().call(refs.syscall, &[rax, v1, v2, v3, v4, v5, v6]);

                tmp.push(bu.inst_results(sysc)[0]);
            }
        }
    }

    // build terminator
    let mut build_return = |bu: &mut FunctionBuilder, next: &analysis::Next| {
        flush(&mut tmp, bu);
        match next {
            analysis::Next::Trap => {
                bu.ins().trap(TrapCode::unwrap_user(67));
            }
            analysis::Next::Terminate => {
                let final_stack = bu.use_var(stack);
                bu.ins().return_(&[final_stack]);
            }
            analysis::Next::Block(block) => {
                bu.ins().jump(block.cranelift_block, &[]);
            }
        }
    };

    let get_block = |next: &analysis::Next| match next {
        analysis::Next::Trap => trap_block,
        analysis::Next::Terminate => term_block,
        analysis::Next::Block(block) => block.cranelift_block,
    };

    match &block.terminator {
        analysis::Terminator::Jump(next) => build_return(bu, next),
        analysis::Terminator::If { on_true, on_false } => {
            let on_true = get_block(on_true);
            let on_false = get_block(on_false);

            let cond = xpop(&mut tmp, bu);

            flush(&mut tmp, bu);
            bu.ins().brif(cond, on_true, &[], on_false, &[]);
        }
        analysis::Terminator::Skip { targets } => {
            let mut switch = Switch::new();

            let targets: Vec<_> = targets.into_iter().map(get_block).collect();
            for (i, block) in targets.into_iter().enumerate() {
                switch.set_entry(i as u128, block);
            }

            let popped = xpop(&mut tmp, bu);

            flush(&mut tmp, bu);
            switch.emit(bu, popped, trap_block);
        }
    }
}

pub(crate) struct ImportRefs {
    printfunc: FuncRef,
    quitfunc: FuncRef,
    errorfunc: FuncRef,
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
pub(crate) struct Callees(HashMap<FuncId, FuncRef>);

impl<T: Module> Compiler<T> {
    pub(crate) fn generate_signature(&self, callconv: CallConv) -> Signature {
        generate_clac_function_signature(self.module.isa(), callconv)
    }

    fn declare_callees(
        &mut self,
        line: &[types::Instr],
        func: &mut cranelift::codegen::ir::Function,
        funcs: &HashMap<&str, FuncId>,
    ) -> Result<Callees, JITError> {
        let mut ret = HashMap::new();

        for instr in line {
            if let Instr::FunctionCall(funcref) = instr
                && let Some(&target) = funcs.get(funcref.0.as_str())
            {
                ret.insert(target, self.module.declare_func_in_func(target, func));
            }
        }

        Ok(Callees(ret))
    }

    pub(crate) fn define_wrapper(
        &mut self,
        name: &str,
        to_wrap: FuncId,
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

        let ret = bu.ins().call(target, &[stack]);
        let ret = bu.inst_results(ret)[0];

        bu.ins().return_(&[ret]);

        bu.finalize();

        self.module.define_function(wrapper_id, ctx)?;

        Ok(wrapper_id)
    }

    pub(crate) fn compile_function(
        function: &[types::Instr],
        mut ctx: cranelift::codegen::Context,
        funcs: &HashMap<&str, FuncId>,
        Callees(callees): Callees,
        isa: &dyn TargetIsa,
        refs: ImportRefs,
    ) -> Result<cranelift::codegen::Context, CompilerError> {
        let mut fbctx = FunctionBuilderContext::new();

        // TODO: fix when better function analysis is added
        ctx.func.signature = generate_clac_function_signature(isa, CallConv::Tail);
        dbg_println!("Callees = {:?}", callees);

        let mut bu = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let analyzed = analysis::create_graph(function, &mut bu);

        let Some(entry) = analyzed.get(&0) else {
            let x = bu.create_block();

            bu.switch_to_block(x);
            bu.append_block_params_for_function_params(x);

            bu.seal_block(x);

            let stack = bu.block_params(x)[0];

            bu.ins().return_(&[stack]);

            bu.finalize();

            dbg_println!("compiled empty function");

            return Ok(ctx);
        };

        // dbg_println!("entry = {:?}", entry);

        let cb = entry.cranelift_block;

        bu.append_block_params_for_function_params(cb);
        bu.switch_to_block(cb);

        let stack = bu.block_params(cb)[0];

        let stack_var = bu.declare_var(isa.pointer_type());
        bu.def_var(stack_var, stack);

        let stack = stack_var;

        let (trap_block, term_block) = (bu.create_block(), bu.create_block());

        for (_, block) in analyzed {
            compile_block(
                block,
                stack,
                &mut bu,
                isa,
                (funcs, &callees),
                (trap_block, term_block),
                &refs,
            );
        }

        // create trap and term block
        bu.switch_to_block(trap_block);
        bu.ins().trap(TrapCode::unwrap_user(67));
        bu.seal_block(trap_block);

        bu.switch_to_block(term_block);
        let stack_final = bu.use_var(stack);
        bu.ins().return_(&[stack_final]);
        bu.seal_block(term_block);

        // TODO: tailcall?
        // if let Some((_, CraneliftedBlock(_, final_block))) = block_map.last_key_value() {
        //     // debug_assert!(final_block)
        //     optimize_tailcall(&mut bu.func);
        // }

        bu.finalize();

        if cfg!(feature = "debug") {
            ctx.set_disasm(true);
        }

        Ok(ctx)
    }
}

fn optimize_tailcall(func: &mut cranelift::codegen::ir::Function) {
    let mut cursor = FuncCursor::new(func);

    while let Some(_cur_block) = cursor.next_block() {
        let mut to_tailcall = None;

        while let Some(inst) = cursor.next_inst() {
            let real = cursor.func.dfg.insts[inst];
            if let InstructionData::Call {
                opcode: _,
                args,
                func_ref,
            } = real
            {
                to_tailcall = Some((inst, args, func_ref));
                continue;
            }
        }

        let Some((badcall, args, func_ref)) = to_tailcall else {
            continue;
        };

        cursor.goto_inst(badcall);

        let pos = cursor.position();
        debug_assert_eq!(pos, CursorPosition::At(badcall));

        let ret = function_results_from_following_jump_path_to_return_unless_side_effect_found(
            &mut cursor,
        );

        cursor.set_position(pos);
        debug_assert_eq!(cursor.position(), CursorPosition::At(badcall));

        let Some(ret_args) = ret else {
            continue;
        };

        // result from our call
        let resulting_stack = cursor.func.dfg.inst_results(badcall);
        // returning to the function
        if ret_args != resulting_stack {
            continue;
        }

        dbg_println!("TAIL CALLING: {to_tailcall:?}");

        let new = cursor.func.dfg.make_inst(InstructionData::Call {
            opcode: cranelift::codegen::ir::Opcode::ReturnCall,
            args,
            func_ref,
        });

        // TODO: BUG IN CRANELIFT DOCUMENTAITON?? it seems to move the cursor forward
        cursor.replace_inst(new);
        let bug_workaround = cursor.prev_inst().unwrap();

        debug_assert_eq!(bug_workaround, new);

        while let Some(next) = cursor.next_inst() {
            let removed = cursor.remove_inst_and_step_back();
            debug_assert_eq!(next, removed);
        }
    }
}

impl<T: Module> Compiler<T> {
    pub(crate) fn compile(
        mut self,
        funcs: &types::FuncMap,
    ) -> Result<(T, HashMap<String, FuncId>), CompilerError> {
        let tail = self.generate_signature(cranelift::prelude::isa::CallConv::Tail);

        let types::Imports {
            printfunc,
            quitfunc,
            powfunc,
            syscallfunc,
            errorfunc,
        } = self.imports;

        let declared: HashMap<&str, FuncId> = funcs
            .iter()
            .map(|(name, _)| {
                (
                    name.as_str(),
                    self.module.declare_anonymous_function(&tail).unwrap(),
                )
            })
            .collect();

        let x: HashMap<
            &str,
            (
                &[types::Instr],
                cranelift::codegen::Context,
                Callees,
                ImportRefs,
            ),
        > = funcs
            .iter()
            .map(|(name, code)| {
                let mut ctx = self.module.make_context();
                let callees = self
                    .declare_callees(code, &mut ctx.func, &declared)
                    .unwrap();
                let refs = ImportRefs {
                    printfunc: self.module.declare_func_in_func(printfunc, &mut ctx.func),
                    quitfunc: self.module.declare_func_in_func(quitfunc, &mut ctx.func),
                    errorfunc: self.module.declare_func_in_func(errorfunc, &mut ctx.func),
                    powfunc: self.module.declare_func_in_func(powfunc, &mut ctx.func),
                    syscall: self.module.declare_func_in_func(syscallfunc, &mut ctx.func),
                };
                (name.as_str(), (code.as_slice(), ctx, callees, refs))
            })
            .collect();

        let isa = self.module.isa();

        let res: HashMap<_, _> = x
            .into_par_iter()
            .map(|(name, (code, ctx, callees, refs))| {
                (
                    name,
                    Self::compile_function(code, ctx, &declared, callees, isa, refs).unwrap(),
                )
            })
            .collect();

        for (name, mut ctx) in res {
            self.module
                .define_function(*declared.get(name).unwrap(), &mut ctx)?;
            dbg_println!("{name} IR: {}", ctx.func.display());

            // dbg_println!(
            //     "Disassembly of {name}: {}",
            //     ctx.compiled_code().unwrap().vcode.as_ref().unwrap()
            // );
        }

        let mut ctx = self.module.make_context();
        let mut fbctx = FunctionBuilderContext::new();

        let out = declared
            .into_iter()
            .map(|(name, id)| {
                (
                    name.to_string(),
                    self.define_wrapper(name, id, &mut ctx, &mut fbctx).unwrap(),
                )
            })
            .collect();

        Ok((self.module, out))
    }
}
