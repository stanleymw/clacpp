use std::{
    collections::{BTreeMap, BTreeSet},
    mem::transmute_copy,
};

use crate::types::{self, Arith, CRANELIFT_VALUE, Function, Instr, JITFunction, JITState};
use cranelift::{
    codegen::ir::FuncRef,
    frontend::Switch,
    prelude::{
        AbiParam, FunctionBuilder, InstBuilder, IntCC, MemFlags, Signature, TrapCode, Value,
        Variable, types::I64,
    },
};

use types::Value as ClacValue;

use cranelift_module::{FuncId, Module, ModuleError, ModuleResult};
use thiserror::Error;

pub enum JITError {
    IndeterminateControlFlow,
}

#[derive(Debug, Error)]
pub(crate) enum CompilerError {
    #[error("Module (cranelift) Error: {0}")]
    ModuleError(#[from] ModuleError),
}

const CLAC_VALUE_STRIDE: i64 = size_of::<ClacValue>() as i64;
const ALIGNED: MemFlags = MemFlags::new().with_aligned();

fn emit_push(bu: &mut FunctionBuilder, stack: Variable, val: Value) {
    let pos = bu.use_var(stack);

    bu.ins().store(ALIGNED, val, pos, 0);

    let new_pos = bu.ins().iadd_imm(pos, CLAC_VALUE_STRIDE);
    bu.def_var(stack, new_pos);
}

fn emit_pop(bu: &mut FunctionBuilder, stack: Variable) -> Value {
    let pos = bu.use_var(stack);
    let new_pos = bu.ins().iadd_imm(pos, -CLAC_VALUE_STRIDE);
    bu.def_var(stack, new_pos);

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
fn debug_simulate_breaks(func: &[types::Instr]) {}

fn get_block_breaks(func: &[types::Instr]) -> Option<BTreeSet<usize>> {
    let mut ret: BTreeSet<usize> = BTreeSet::new();

    let insert_checked = |set: &mut BTreeSet<usize>, val: usize| -> Option<bool> {
        if val <= func.len() {
            Some(set.insert(val))
        } else {
            None
        }
    };

    for (i, instr) in func.iter().enumerate() {
        println!("{} {:?}", i, instr);
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
                    let conv: usize = (*n).try_into().ok()?;

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

    Some(ret)
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
    block: (usize, &ClacBlock),
    total_len: usize,
    blockmap: &BlockMap,
    stack: Variable,
    bu: &mut FunctionBuilder,
    refs: &ImportRefs,
) {
    println!("compiling block = {:?}", block);
    let (head, ClacBlock(line, block)) = block;
    let line = *line;
    let block = *block;

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

    let xpick = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
        let popped = xpop(tmp, bu);
        flush(tmp, bu);

        emit_pick(bu, stack, popped);
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
                    Arith::Add => bu.ins().iadd(a, b),
                    Arith::Sub => bu.ins().isub(a, b),
                    Arith::Mul => bu.ins().imul(a, b),
                    Arith::Div => bu.ins().sdiv(a, b),
                    Arith::Rem => bu.ins().srem(a, b),
                    Arith::Lt => bu.ins().icmp(IntCC::SignedLessThan, a, b),
                    Arith::Pow => {
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
                xpop(&mut tmp, bu);
            }
            Instr::Print => {
                let popped = xpop(&mut tmp, bu);
                bu.ins().call(refs.printfunc, &[popped]);
            }
            Instr::Quit => {
                bu.ins().call(refs.quitfunc, &[]);
            }
            Instr::Pick => xpick(&mut tmp, bu),
            Instr::If => {
                debug_assert!((&line[i + 1..]).len() == 0);
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
                    let pop = xpop(&mut tmp, bu);
                    // TODO: assert popped == n

                    // no break here, we can use constant optimization
                    let conv: usize = (*n).try_into().ok().unwrap();

                    let new: usize = real_i + conv + 1;
                    let target = blockmap.get(&new).unwrap().1;

                    flush(&mut tmp, bu);
                    bu.ins().jump(target, &[]);

                    return;
                } else {
                    debug_assert!((&line[i + 1..]).len() == 0);
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
            _ => todo!(),
        }
    }

    flush(&mut tmp, bu);

    if line.len() != 0
        && let Some(next) = blockmap.get(&(head + line.len()))
    {
        println!("GOT NEXT = {:?}", next);

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
}

impl JITState {
    pub(crate) fn get_function(&self, func: FuncId) -> JITFunction {
        unsafe { transmute_copy(&self.module.get_finalized_function(func)) }
    }

    fn generate_signature(&self) -> Signature {
        let ptr_t = self.module.isa().pointer_type();
        let ptr_arg = AbiParam::new(ptr_t);

        Signature {
            params: vec![ptr_arg],  // *mut ClacValue
            returns: vec![ptr_arg], // *mut ClacValue
            call_conv: self.module.isa().default_call_conv(),
        }
    }

    pub(crate) fn compile_function(
        &mut self,
        id: FuncId,
        line: &[types::Instr],
    ) -> Result<(), CompilerError> {
        let sig = self.generate_signature();
        let types::JITState {
            ctx,
            fbctx,
            module,
            imports:
                types::Imports {
                    printfunc,
                    quitfunc,
                    errorfunc,
                    powfunc,
                },
        } = self;

        module.clear_context(ctx);
        ctx.func.signature = sig;

        let refs = ImportRefs {
            printfunc: module.declare_func_in_func(*printfunc, &mut ctx.func),
            quitfunc: module.declare_func_in_func(*quitfunc, &mut ctx.func),
            errorfunc: module.declare_func_in_func(*errorfunc, &mut ctx.func),
            powfunc: module.declare_func_in_func(*powfunc, &mut ctx.func),
        };

        let breaks = get_block_breaks(line).unwrap();
        println!("{:?}", breaks);
        let slice_map = breaks_to_slicemap(breaks, line);
        println!("{:?}", slice_map);

        let mut bu = FunctionBuilder::new(&mut ctx.func, fbctx);

        let block_map = make_blockmap(slice_map, &mut bu);
        println!("{:?}", block_map);

        let ClacBlock(_, entry) = block_map.get(&0).unwrap();

        let entry = *entry;
        bu.switch_to_block(entry);
        println!("entry = {}", entry);
        bu.append_block_params_for_function_params(entry);

        let stack = bu.block_params(entry)[0];

        let stack_var = bu.declare_var(module.isa().pointer_type());
        bu.def_var(stack_var, stack);

        let stack = stack_var;

        for (i, block) in &block_map {
            compile_block((*i, block), line.len(), &block_map, stack, &mut bu, &refs);
        }

        // bu.seal_all_blocks(); // FIXME: investigate
        bu.finalize();

        // TODO: if cranelift adds an ability to free previously declared functions, we should do that.
        module.define_function(id, ctx)?;

        Ok(())
    }
}

impl types::ClacState {
    pub(crate) fn declare_and_compile_all_functions(&mut self) -> ModuleResult<()> {
        // declare all functions
        self.declare_functions_in_jit_module()?;

        // compile all functions
        self.compile_all()?;

        self.jit.module.finalize_definitions()?;

        Ok(())
    }

    pub(crate) fn compile_all(&mut self) -> ModuleResult<()> {
        for function in &mut self.funcmap.functions {
            if let Function::User(fid, code) = function {
                match self.jit.compile_function((*fid).unwrap(), code) {
                    Ok(()) => {
                        println!("Successfully compiled {fid:?} (code = {code:?})");
                    }
                    Err(err) => {
                        println!("Could not compile {fid:?} because {err} (code = {code:?})",);
                        *fid = None;
                    }
                }
            }
        }
        Ok(())
    }

    pub(crate) fn declare_functions_in_jit_module(&mut self) -> ModuleResult<()> {
        let sig = self.jit.generate_signature();

        for function in &mut self.funcmap.functions {
            if let Function::User(funcid, _) = function {
                *funcid = Some(self.jit.module.declare_anonymous_function(&sig)?);
            }
        }

        Ok(())
    }
}
