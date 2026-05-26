use cranelift::codegen::{inline::Inline, ir::Function};

pub struct ClacInliner {}

impl Inline for ClacInliner {
    fn inline(
        &mut self,
        caller: &cranelift::codegen::ir::Function,
        call_inst: cranelift::codegen::ir::Inst,
        call_opcode: cranelift::codegen::ir::Opcode,
        callee: cranelift::codegen::ir::FuncRef,
        call_args: &[cranelift::codegen::ir::Value],
    ) -> cranelift::codegen::inline::InlineCommand<'_> {
        cranelift::codegen::inline::InlineCommand::Inline {
            callee: todo!(), // FIXME: after implementing the layered topological sort idea, use that for the order
            visit_callee: true,
        }
    }
}
