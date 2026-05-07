use ahash::{HashMap, HashMapExt};
use cranelift::codegen::{
    cursor::{Cursor, CursorPosition, FuncCursor},
    ir::{BlockArg, InstructionData, Opcode},
};

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

fn trivially_has_side_effects(opcode: cranelift::codegen::ir::Opcode) -> bool {
    opcode.is_call()
        || opcode.is_branch()
        || opcode.is_terminator()
        || opcode.is_return()
        || opcode.can_trap()
        || opcode.other_side_effects()
        || opcode.can_store()
    // || opcode.can_load()
}

// we need to make sure this return is the same as the resulting stack
pub(crate) fn function_results_from_following_jump_path_to_return_unless_side_effect_found(
    cursor: &mut FuncCursor,
) -> Option<Vec<cranelift::prelude::Value>> {
    let mut mapper = HashMap::new();

    while let Some(inst) = cursor.next_inst() {
        let real = cursor.func.dfg.insts[inst];
        // Ensure that the remaining functions do no side effects, and that the terminator == return || ALWAYS GOES TO the END BLOCK

        match real {
            InstructionData::Jump {
                opcode: cranelift::codegen::ir::Opcode::Jump,
                destination: bc,
            } => {
                let out = bc.block(&cursor.func.dfg.value_lists);

                let jump_args = bc.args(&cursor.func.dfg.value_lists);
                let block_args = cursor.func.dfg.block_params(out);

                mapper.extend(block_args.iter().copied().zip(jump_args.map(|blockarg| {
                    let BlockArg::Value(x) = blockarg else {
                        panic!("Not value blockarg")
                    };
                    x
                })));

                cursor.set_position(CursorPosition::Before(out));
            }
            InstructionData::MultiAry {
                opcode: Opcode::Return,
                args: elist,
            } => {
                let mut ret = Vec::new();

                dbg_println!("RESOLVED RETS: {mapper:?}");

                for mut arg in elist.as_slice(&cursor.func.dfg.value_lists) {
                    // resolve fully
                    while let Some(next) = mapper.get(arg) {
                        arg = next;
                    }

                    ret.push(*arg);
                }

                return Some(ret);
            }
            x if trivially_has_side_effects(x.opcode()) => return None,
            _ => {}
        }
    }
    unreachable!();
}
