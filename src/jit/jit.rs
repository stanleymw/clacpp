use std::{
    collections::{BTreeMap, BTreeSet},
    mem::transmute_copy,
};

use crate::{
    jit::analysis::function_results_from_following_jump_path_to_return_unless_side_effect_found,
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
        AbiParam, FunctionBuilder, InstBuilder, IntCC, MemFlags, Signature, TrapCode, Value,
        Variable,
        isa::{CallConv, TargetIsa},
        types::I64,
    },
};

use cranelift_jit::JITModule;
use types::Function as ClacFunction;
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

#[cfg(debug_assertions)]
// TODO: implement this
fn _debug_simulate_breaks(_func: &[types::Instr]) {}

fn get_block_breaks(func: &[types::Instr]) -> Result<BTreeSet<usize>, JITError> {
    let mut ret: BTreeSet<usize> = BTreeSet::new();

    let insert_checked = |set: &mut BTreeSet<usize>, val: usize| -> Result<bool, JITError> {
        if val <= func.len() {
            Ok(set.insert(val))
        } else {
            Err(JITError::IndeterminateControlFlow)
        }
    };

    for (i, instr) in func.iter().enumerate() {
        dbg_println!("{} {:?}", i, instr);
        match instr {
            Instr::If => {
                // you can jump ahead by a fixed amount
                insert_checked(&mut ret, i + 4)?;
                insert_checked(&mut ret, i + 1)?;
            }
            Instr::Skip => {
                // 2 cases:
                // if there is no BREAK at this position, and the previous value is a constant, then we are guaranteed to know how much we are going to jump by.
                // assuming that we have found all of the breaks up to this point. (TODO: PROVE THIS IS CORRECT)
                if !ret.contains(&i)
                    && i > 0
                    && let Some(Instr::Literal(n)) = func.get(i - 1)
                {
                    // no break here, we can use constant optimization
                    let conv: usize = (*n).try_into().map_err(|_| JITError::BadSkip)?;

                    let new: usize = i + conv + 1;
                    insert_checked(&mut ret, new)?;
                } else {
                    for new in (i + 1)..=func.len() {
                        ret.insert(new);
                    }
                }
            }
            _ => {}
        }
    }

    for i in &ret {
        debug_assert!(*i <= func.len());
    }

    Ok(ret)
}

fn breaks_to_slicemap(
    breaks: BTreeSet<usize>,
    line: &[types::Instr],
) -> BTreeMap<usize, &[types::Instr]> {
    let mut last: usize = 0;
    let mut res = BTreeMap::new();
    for br in breaks {
        res.insert(last, &line[last..br]);
        last = br
    }
    res.insert(last, &line[last..]);

    res
}

#[derive(Debug)]
struct ClacBlock<'a>(&'a [types::Instr], cranelift::prelude::Block);

type BlockMap<'a> = BTreeMap<usize, ClacBlock<'a>>;

fn make_blockmap<'a>(
    tree: BTreeMap<usize, &'a [types::Instr]>,
    bu: &mut FunctionBuilder,
) -> BlockMap<'a> {
    tree.iter()
        .map(|(i, instrs)| (*i, ClacBlock(instrs, bu.create_block())))
        .collect()
}

fn compile_block(
    (head, &ClacBlock(line, block)): (usize, &ClacBlock),
    isa: &dyn TargetIsa,
    total_len: usize,
    blockmap: &BlockMap,
    calleemap: &HashMap<FuncId, FuncRef>,
    funcs: &types::FuncMap,
    stack: Variable,
    bu: &mut FunctionBuilder,
    refs: &ImportRefs,
) {
    dbg_println!("compiling block = {:?}", block);

    bu.switch_to_block(block);
    bu.seal_block(block);

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

    let is_last_block = head == *blockmap.last_key_value().unwrap().0;

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

    for (i, inst) in line.iter().enumerate() {
        use types::Instr;
        let real_i = head + i;

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
            Instr::If => {
                debug_assert!(i == line.len() - 1);

                let cond = xpop(&mut tmp, bu);

                let success = blockmap.get(&(real_i + 1)).unwrap().1;
                let fail = blockmap.get(&(real_i + 4)).unwrap().1;

                flush(&mut tmp, bu);
                bu.ins().brif(cond, success, &[], fail, &[]);

                return;
            }
            Instr::Skip => {
                if i > 0
                    && let Some(Instr::Literal(n)) = line.get(i - 1)
                {
                    assert_eq!(value_to_const(bu.func, tmp.pop().unwrap()).unwrap(), *n);

                    // no break here, we can use constant optimization
                    let conv: usize = (*n).try_into().ok().unwrap();

                    let new: usize = real_i + conv + 1;
                    let target = blockmap.get(&new).unwrap().1;

                    flush(&mut tmp, bu);
                    bu.ins().jump(target, &[]);

                    return;
                } else {
                    debug_assert!(i == line.len() - 1);
                    let mut switch = Switch::new();

                    let start = real_i + 1;
                    for new in start..=total_len {
                        let found = blockmap.get(&new).unwrap().1;
                        switch.set_entry((new - start) as u128, found);
                    }
                    let popped = xpop(&mut tmp, bu);

                    // FIXME: dont create duplicates
                    let abort = bu.create_block();

                    flush(&mut tmp, bu);
                    switch.emit(bu, popped, abort);

                    bu.switch_to_block(abort);
                    bu.seal_block(abort);
                    bu.ins().trap(TrapCode::unwrap_user(67));

                    return;
                };
            }
            Instr::FunctionCall(func) => {
                let Some(func) = funcs.lookup(func) else {
                    dbg_println!("TRYING TO CALL UNRESOLVED FUNCTION: {func:?}");
                    bu.ins().trap(TrapCode::unwrap_user(67));
                    return;
                };

                let func = calleemap[&func.id];

                flush(&mut tmp, bu);
                let final_stack = bu.use_var(stack);

                // if i == line.len() - 1 && is_last_block {
                //     bu.ins().return_call(*func, &[final_stack]);
                //     return;
                // }

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

    flush(&mut tmp, bu);

    if !is_last_block && let Some(next) = blockmap.get(&(head + line.len())) {
        dbg_println!("GOT NEXT = {:?}", next);

        flush(&mut tmp, bu);
        bu.ins().jump(next.1, &[]);
    } else {
        // assert(FINAL BLOCK)
        debug_assert!(head + line.len() == total_len);

        flush(&mut tmp, bu);
        let final_stack = bu.use_var(stack);
        bu.ins().return_(&[final_stack]);
    }
}

struct ImportRefs {
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

impl Compiler<JITModule> {
    pub(crate) fn get_function(&self, func: FuncId) -> JITFunction {
        unsafe { transmute_copy(&self.module.get_finalized_function(func)) }
    }
}

impl<T: Module> Compiler<T> {
    pub(crate) fn generate_signature(&self, callconv: CallConv) -> Signature {
        generate_clac_function_signature(self.module.isa(), callconv)
    }

    fn build_callee_map(
        &mut self,
        line: &[types::Instr],
        funcs: &types::FuncMap,
    ) -> Result<HashMap<FuncId, FuncRef>, JITError> {
        let mut ret = HashMap::new();

        for instr in line {
            if let Instr::FunctionCall(funcref) = instr
                && let Some(target) = funcs.lookup(funcref)
            {
                let ClacFunction { id, .. } = target;
                ret.insert(
                    *id,
                    self.module.declare_func_in_func(*id, &mut self.ctx.func),
                );
            }
        }

        Ok(ret)
    }

    pub(crate) fn define_wrapper(&mut self, function: &ClacFunction) -> ModuleResult<()> {
        self.module.clear_context(&mut self.ctx);

        // TODO: fix
        self.ctx.func.signature = self.generate_signature(self.module.isa().default_call_conv());

        let target = self
            .module
            .declare_func_in_func(function.id, &mut self.ctx.func);

        let mut bu = FunctionBuilder::new(&mut self.ctx.func, &mut self.fbctx);
        let entry = bu.create_block();
        bu.switch_to_block(entry);
        bu.seal_block(entry);

        bu.append_block_params_for_function_params(entry);

        let stack = bu.block_params(entry)[0];

        let ret = bu.ins().call(target, &[stack]);
        let ret = bu.inst_results(ret)[0];

        bu.ins().return_(&[ret]);

        bu.finalize();

        self.module
            .define_function(function.wrapper_id, &mut self.ctx)?;

        Ok(())
    }

    pub(crate) fn define_function(
        &mut self,
        function: &ClacFunction,
        funcs: &types::FuncMap,
    ) -> Result<(), CompilerError> {
        self.module.clear_context(&mut self.ctx);

        // TODO: fix
        self.ctx.func.signature = self.generate_signature(CallConv::Tail);

        let callees = self.build_callee_map(&function.code, funcs)?;

        dbg_println!("Callees = {:?}", callees);

        let types::Compiler {
            ctx,
            fbctx,
            module,
            imports:
                types::Imports {
                    printfunc,
                    quitfunc,
                    errorfunc,
                    powfunc,
                    syscallfunc,
                },
        } = self;

        let refs = ImportRefs {
            printfunc: module.declare_func_in_func(*printfunc, &mut ctx.func),
            quitfunc: module.declare_func_in_func(*quitfunc, &mut ctx.func),
            errorfunc: module.declare_func_in_func(*errorfunc, &mut ctx.func),
            powfunc: module.declare_func_in_func(*powfunc, &mut ctx.func),
            syscall: module.declare_func_in_func(*syscallfunc, &mut ctx.func),
        };

        let breaks = get_block_breaks(&function.code)?;
        dbg_println!("{:?}", breaks);

        let slice_map = breaks_to_slicemap(breaks, &function.code);
        dbg_println!("{:?}", slice_map);

        let mut bu = FunctionBuilder::new(&mut ctx.func, fbctx);

        let block_map = make_blockmap(slice_map, &mut bu);
        dbg_println!("{:?}", block_map);

        let ClacBlock(_, entry) = block_map.get(&0).unwrap();

        let entry = *entry;
        bu.switch_to_block(entry);
        dbg_println!("entry = {}", entry);
        bu.append_block_params_for_function_params(entry);

        let stack = bu.block_params(entry)[0];

        let stack_var = bu.declare_var(module.isa().pointer_type());
        bu.def_var(stack_var, stack);

        let stack = stack_var;

        for (i, block) in &block_map {
            compile_block(
                (*i, block),
                module.isa(),
                function.code.len(),
                &block_map,
                &callees,
                funcs,
                stack,
                &mut bu,
                &refs,
            );
        }

        dbg_println!("Before tailcall IR: {}", bu.func.display());

        if let Some((_, ClacBlock(_, final_block))) = block_map.last_key_value() {
            // debug_assert!(final_block)
            optimize_tailcall(&mut bu.func);
        }

        bu.finalize();

        dbg_println!("Unoptimized IR: {}", ctx.func.display());

        if cfg!(feature = "debug") {
            ctx.set_disasm(true);
        }

        module.define_function(function.id, ctx)?;

        dbg_println!("Optimized IR: {}", ctx.func.display());

        dbg_println!(
            "disasm: {}",
            ctx.compiled_code().unwrap().vcode.as_ref().unwrap()
        );

        Ok(())
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
    pub(crate) fn compile_functions_and_wrappers(
        &mut self,
        funcs: &types::FuncMap,
    ) -> Result<(), CompilerError> {
        for (_, function) in &funcs.0 {
            self.define_function(&function, &funcs)?;
            self.define_wrapper(&function)?;
        }
        Ok(())
    }
}
