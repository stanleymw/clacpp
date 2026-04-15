use std::mem::transmute_copy;

use crate::types::{self, CRANELIFT_VALUE};
use cranelift::prelude::{
    AbiParam, FunctionBuilder, InstBuilder, MemFlags, Signature, Value, Variable, types::I64,
};

use types::Value as ClacValue;

use cranelift_module::{Linkage, Module, ModuleError};
use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum CompilerError {
    #[error("Module (cranelift) Error: {0}")]
    ModuleError(#[from] ModuleError),
}

fn emit_push(bu: &mut FunctionBuilder, stack: Variable, val: Value) {
    let pos = bu.use_var(stack);

    bu.ins().store(MemFlags::new().with_aligned(), val, pos, 0);

    let new_pos = bu.ins().iadd_imm(pos, size_of::<ClacValue>() as i64);
    bu.def_var(stack, new_pos);
}

fn emit_pop(bu: &mut FunctionBuilder, stack: Variable) -> Value {
    let pos = bu.use_var(stack);
    let new_pos = bu.ins().iadd_imm(pos, -(size_of::<ClacValue>() as i64));
    bu.def_var(stack, new_pos);

    bu.ins()
        .load(CRANELIFT_VALUE, MemFlags::new().with_aligned(), new_pos, 0)
}
impl types::ClacState {
    pub(crate) fn compile_function(
        &mut self,
        line: &[types::Instr],
    ) -> Result<types::JITFunction, CompilerError> {
        let types::JITState {
            ctx,
            fbctx,
            module,
            imports:
                types::Imports {
                    printfunc,
                    quitfunc,
                },
        } = &mut self.jit;

        module.clear_context(ctx);

        let ptr_t = module.isa().pointer_type();
        let ptr_arg = AbiParam::new(ptr_t);

        ctx.func.signature = Signature {
            params: vec![ptr_arg],  // *mut ClacValue
            returns: vec![ptr_arg], // *mut ClacValue
            call_conv: module.isa().default_call_conv(),
        };

        let printfunc = module.declare_func_in_func(*printfunc, &mut ctx.func);
        let quitfunc = module.declare_func_in_func(*quitfunc, &mut ctx.func);

        let mut bu = FunctionBuilder::new(&mut ctx.func, fbctx);

        let entry = bu.create_block();
        bu.append_block_params_for_function_params(entry);
        bu.switch_to_block(entry);
        bu.seal_block(entry);

        // Idea:
        // 2 levels of stack
        // there is the REAL stack (passed in pointer)
        // and also a build/function stack (*mut ClacStack)
        //
        // Before if statements/control flow, we commit/flush the build function stack, which means pushing everything onto the build function stack onto the real stack.
        // if we get to the final block, then we geneate instructions to push all of the build stack onto the REAL stack.
        // must also flush before Pick
        //
        // then every function is fn(*mut ClacStack) -> ()
        let stack = bu.block_params(entry)[0];
        let stack_var = bu.declare_var(module.isa().pointer_type());
        bu.def_var(stack_var, stack);
        let stack = stack_var;

        let mut tmp: Vec<Value> = Vec::new();

        let flush = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
            for val in &*tmp {
                emit_push(bu, stack, *val);
            }

            tmp.clear();
        };

        // let mut xpush = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
        //     tmp.pop().unwrap_or_else(|| {
        //         let call_instr = bu.ins().call(popper, &[stack]);
        //     })
        // };

        let xpop = |tmp: &mut Vec<Value>, bu: &mut FunctionBuilder| {
            tmp.pop().unwrap_or_else(|| emit_pop(bu, stack))
        };

        for inst in line {
            use types::Instr;
            match inst {
                Instr::Literal(n) => {
                    let out = bu.ins().iconst(I64, *n);
                    tmp.push(out);
                }
                it @ (Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | Instr::Rem) => {
                    let b = xpop(&mut tmp, &mut bu);
                    let a = xpop(&mut tmp, &mut bu);

                    tmp.push(match it {
                        Instr::Add => bu.ins().iadd(a, b),
                        Instr::Sub => bu.ins().isub(a, b),
                        Instr::Mul => bu.ins().imul(a, b),
                        Instr::Div => bu.ins().sdiv(a, b),
                        Instr::Rem => bu.ins().srem(a, b),
                        _ => unreachable!(),
                    });
                }
                Instr::Swap => {
                    let b = xpop(&mut tmp, &mut bu);
                    let a = xpop(&mut tmp, &mut bu);

                    tmp.push(b);
                    tmp.push(a);
                }
                Instr::Rot => {
                    let z = xpop(&mut tmp, &mut bu);
                    let y = xpop(&mut tmp, &mut bu);
                    let x = xpop(&mut tmp, &mut bu);

                    tmp.push(y);
                    tmp.push(z);
                    tmp.push(x);
                }
                Instr::Drop => {
                    xpop(&mut tmp, &mut bu);
                }
                Instr::Print => {
                    let popped = xpop(&mut tmp, &mut bu);
                    bu.ins().call(printfunc, &[popped]);
                }
                Instr::Quit => {
                    bu.ins().call(quitfunc, &[]);
                }
                _ => todo!(),
            }
        }

        flush(&mut tmp, &mut bu);

        let final_stack = bu.use_var(stack);
        let _ret = bu.ins().return_(&[final_stack]);

        bu.seal_all_blocks(); // FIXME: investigate
        bu.finalize();

        println!("Pre-optimize: {}", ctx.func.display());

        // TODO: if cranelift adds an ability to free previously declared functions, we should do that.
        let id = module.declare_anonymous_function(&ctx.func.signature)?;
        module.define_function(id, ctx)?;

        module.finalize_definitions()?;

        let fun = module.get_finalized_function(id);

        println!("Optimized: {}", ctx.func.display());
        println!("JIT compiled function = {:?}", fun);

        Ok(unsafe { transmute_copy(&fun) })
    }
}
