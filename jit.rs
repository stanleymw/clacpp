use cranelift::prelude::{
    AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature,
    isa::IsaBuilder, settings, types::I64,
};
use cranelift_jit::JITBuilder;
use cranelift_module::Module;

pub fn execute_tokens_2(&mut self, line: &[Instr]) -> Result<(), ExecError> {
    let builder = JITBuilder::with_flags(
        &[("opt_level", "speed")],
        cranelift_module::default_libcall_names(),
    )
    .unwrap();

    let mut module = cranelift_jit::JITModule::new(builder);
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();

    ctx.func.signature = Signature {
        params: vec![AbiParam::new(module.isa().pointer_type())],
        returns: vec![],
        call_conv: cranelift::prelude::isa::CallConv::SystemV,
    };

    let mut bu = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

    let b0 = bu.create_block();

    bu.switch_to_block(b0);
    bu.seal_block(b0);

    let mut vals = Vec::new();

    // Idea:
    // 2 levels of stack
    // there is the REAL stack (passed in pointer)
    // and also a build/function stack (*mut ClacStack)
    // Before if statements/control flow, we commit/flush the build function stack, which means pushing everything onto the build function stack onto the real stack.
    // if we get to the final block, then we geneate instructions to push all of the build stack onto the REAL stack.
    // then every function is fn(*mut ClacStack) -> ()

    for tok in line {
        match tok {
            Instr::Literal(n) => {
                vals.push(bu.ins().iconst(I64, *n));
            }
            Instr::FunctionCall(FunctionRef(InternalFunctionRef::Unresolved(n))) => {
                let b = vals.pop().unwrap();
                let a = vals.pop().unwrap();
                match &**n {
                    "+" => vals.push(bu.ins().iadd(a, b)),
                    "-" => vals.push(bu.ins().isub(a, b)),
                    "*" => vals.push(bu.ins().imul(a, b)),
                    "/" => vals.push(bu.ins().sdiv(a, b)),
                    "%" => vals.push(bu.ins().srem(a, b)),
                    _ => panic!(),
                }
            }
            _ => unimplemented!(),
        }
    }

    let _ret = bu.ins().return_(&[]);

    bu.seal_all_blocks(); // FIXME: investigate

    bu.finalize();

    println!("{}", ctx.func.display());

    let dec = module
        .declare_anonymous_function(&ctx.func.signature)
        .unwrap();
    module.define_function(dec, &mut ctx).unwrap();

    // println!("finalize = {:?}", module.finalize_definitions());
    module.finalize_definitions().unwrap();

    let fun = module.get_finalized_function(dec);

    let casted: extern "C" fn(*mut ValueStack) = unsafe { transmute(fun) };

    println!("fn = {casted:?}");
    // println!("result = {}", casted());

    Ok(())
}
