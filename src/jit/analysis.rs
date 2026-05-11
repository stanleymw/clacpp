use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use ahash::{HashMap, HashMapExt};
use cranelift::codegen::{
    cursor::{Cursor, CursorPosition, FuncCursor},
    ir::{BlockArg, InstructionData, Opcode},
};

use crate::types::{self, Instr};

#[derive(Debug)]
pub(crate) struct Code<'inst, const NO_CONTROL_FLOW_INSTRUCTIONS: bool>(pub(crate) &'inst [Instr]);

#[derive(Debug)]
pub(crate) enum Terminator<'inst> {
    Jump(Next<'inst>),
    If {
        on_true: Next<'inst>,
        on_false: Next<'inst>,
    },
    Skip {
        targets: Vec<Next<'inst>>,
    },
}

#[derive(Debug)]
pub(crate) enum Next<'inst> {
    Trap,
    Terminate,
    Block(Rc<Block<'inst>>),
}

#[derive(Debug)]
// Each variant is the type of terminator
pub(crate) struct Block<'inst> {
    pub(crate) code: Code<'inst, true>,
    pub(crate) cranelift_block: cranelift::prelude::Block,
    pub(crate) terminator: Terminator<'inst>,
}

impl<'inst> TryFrom<&'inst [types::Instr]> for Code<'inst, true> {
    type Error = ();

    fn try_from(value: &'inst [types::Instr]) -> Result<Self, Self::Error> {
        for val in value {
            match val {
                Instr::If | Instr::Skip => return Err(()),
                _ => (),
            }
        }

        Ok(Self(value))
    }
}

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

#[cfg(debug_assertions)]
// TODO: implement this
fn _debug_simulate_breaks(_func: &[types::Instr]) {}

fn get_block_breaks_v2(func: &[types::Instr]) -> BTreeSet<usize> {
    let mut breaks = BTreeSet::new();

    for (i, instr) in func.iter().enumerate() {
        dbg_println!("{} {:?}", i, instr);

        match instr {
            Instr::If => {
                breaks.insert(i + 4);

                // end the block
                breaks.insert(i + 1);
            }
            Instr::Skip => {
                // 2 cases:
                // if there is no BREAK at this position, and the previous value is a constant, then we are guaranteed to know how much we are going to jump by.
                // assuming that we have found all of the breaks up to this point. (TODO: PROVE THIS IS CORRECT)
                if !breaks.contains(&i)
                    && i > 0
                    && let Some(Instr::Literal(n)) = func.get(i - 1)
                    && let Ok(conv) = usize::try_from(*n)
                {
                    // end the block
                    breaks.insert(i + 1);

                    // no break here, we can use constant optimization
                    let new: usize = i + conv + 1;
                    breaks.insert(new);
                } else {
                    breaks.extend((i + 1)..=func.len());
                }
            }
            _ => {}
        }
    }

    breaks
}

// TODO wip:
// pub fn remove_dangling_blocks(function: &mut BTreeMap<usize, Rc<Block>>) {
//     function.retain(|_, block| {
//         dbg!(&block, Rc::strong_count(&block));
//         Rc::strong_count(&block) > 0
//     });
// }

pub(crate) fn create_graph<'inst>(
    func: &'inst [types::Instr],
    bu: &mut cranelift::prelude::FunctionBuilder,
) -> BTreeMap<usize, Rc<Block<'inst>>> {
    let breaks: Vec<usize> = get_block_breaks_v2(func).into_iter().collect();
    debug_assert!(breaks.is_sorted());

    dbg_println!("breaks = {:?}", breaks);

    // create initial basic blocks
    let mut basic_blocks: Vec<(usize, &[types::Instr])> = Vec::new();
    let mut last: usize = 0;
    for mut br in breaks {
        if last == func.len() {
            break;
        };

        br = std::cmp::min(br, func.len());
        basic_blocks.push((last, &func[last..br]));
        last = br
    }
    if last != func.len() {
        basic_blocks.push((last, &func[last..]));
    }

    dbg_println!("basic blocks = {:?}", basic_blocks);

    let mut out: BTreeMap<usize, Rc<Block>> = BTreeMap::new();

    let get_next = |out: &BTreeMap<usize, Rc<Block<'inst>>>, idx: usize| {
        if idx > func.len() {
            return Next::Trap;
        } else if idx == func.len() {
            return Next::Terminate;
        }

        return Next::Block(out.get(&idx).unwrap().clone());
    };

    // NOTE: it is important that this is reversed, we are exploiting the fact that it is impossible for a clac program to jump backward
    for (start, code) in basic_blocks.into_iter().rev() {
        let (last, begin) = code.split_last().expect("basic_block.len() >= 1");

        match last {
            Instr::If => {
                let new = Block {
                    code: begin.try_into().unwrap(),
                    cranelift_block: bu.create_block(),
                    terminator: Terminator::If {
                        on_true: get_next(&out, start + code.len()),
                        on_false: get_next(&out, start + code.len() + 3),
                    },
                };

                out.insert(start, Rc::new(new));
            }
            Instr::Skip
                if let Some((Instr::Literal(amt), begin2)) = begin.split_last()
                    && let Ok(conv) = usize::try_from(*amt) =>
            {
                let new = Block {
                    code: begin2.try_into().unwrap(),
                    cranelift_block: bu.create_block(),
                    terminator: Terminator::Jump(get_next(&out, start + code.len() + conv)),
                };

                out.insert(start, Rc::new(new));
            }
            Instr::Skip => {
                let new = Block {
                    code: begin.try_into().unwrap(),
                    cranelift_block: bu.create_block(),
                    terminator: Terminator::Skip {
                        targets: ((start + code.len())..=func.len())
                            .map(|val| get_next(&out, val))
                            .collect(),
                    },
                };

                out.insert(start, Rc::new(new));
            }
            _ => {
                let new = Block {
                    code: code.try_into().unwrap(),
                    cranelift_block: bu.create_block(),
                    terminator: Terminator::Jump(get_next(&out, start + code.len())),
                };

                out.insert(start, Rc::new(new));
            }
        };
    }

    // dbg_println!("{:?}", out);

    out
}

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
