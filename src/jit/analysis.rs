use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use ahash::{HashMap, HashMapExt};

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

use crate::types::{self, BasicBlockInstr, ControlFlowInstr, Instr};

#[derive(Debug)]
pub(crate) enum Terminator {
    Jump(Next),
    If { on_true: Next, on_false: Next },
    Skip { targets: Vec<Next> },
}

#[derive(Debug)]
pub(crate) enum Next {
    Trap,
    Terminate,
    Block(Rc<Block>),
}

#[derive(Debug)]
/// A resolved function signature
pub(crate) struct ResolvedSig {
    pub(crate) argc: usize,
    pub(crate) retc: usize,
}

impl ResolvedSig {
    pub fn delta(&self) -> i64 {
        -(self.argc as i64) + (self.retc as i64)
    }

    pub fn reach(&self) -> usize {
        self.argc
    }
}

#[derive(Debug)]
pub(crate) struct Z3Sig {
    argc: Z3Int,
    retc: Z3Int,
}

impl Z3Sig {
    pub fn delta(&self) -> Z3Int {
        -self.argc.clone() + self.retc.clone()
    }

    pub fn reach(&self) -> Z3Int {
        self.argc.clone()
    }
}

#[derive(Debug)]
// Each variant is the type of terminator
pub(crate) struct Block {
    // FIXME: this could be Cow
    pub(crate) code: Vec<BasicBlockInstr>,
    pub(crate) sig: Option<Z3Sig>,
    pub(crate) terminator: Terminator,
}

fn to_basic_block_code<'a>(block: &'a [Instr]) -> Result<Vec<BasicBlockInstr>, &'a types::Instr> {
    let mut res = Vec::new();

    for (i, instr) in block.iter().enumerate() {
        let Instr::BBInstr(conv) = instr else {
            return Err(instr);
        };

        let out = match conv {
            // resolve drop range
            BasicBlockInstr::BadDropRange
                if i >= 2
                    && let &[
                        Instr::BBInstr(BasicBlockInstr::Literal(start)),
                        Instr::BBInstr(BasicBlockInstr::Literal(amt)),
                    ] = &block[i - 2..i]
                    && let Ok(start) = start.try_into()
                    && let Ok(amt) = amt.try_into() =>
            {
                let BasicBlockInstr::Literal(x) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, amt);

                let BasicBlockInstr::Literal(x) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, start);

                assert!(start >= amt);

                BasicBlockInstr::ResolvedDropRange { start, amt }
            }
            // resolve pick
            BasicBlockInstr::BadPick
                if i >= 1
                    && let Instr::BBInstr(BasicBlockInstr::Literal(n)) = block[i - 1]
                    && let Ok(n) = n.try_into() =>
            {
                let BasicBlockInstr::Literal(x) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, n);

                assert!(n >= 1);
                BasicBlockInstr::ResolvedPick(n)
            }
            x => x.clone(),
        };

        res.push(out);
    }

    Ok(res)
}

use z3::ast::Int as Z3Int;

fn max(a: Z3Int, b: Z3Int) -> Z3Int {
    let cond = a.gt(&b);
    cond.ite(&a, &b)
}

fn get_delta_and_reach(
    block: &[BasicBlockInstr],
    known: &HashMap<&str, ResolvedSig>,
    scc: &HashMap<&str, Z3Sig>,
) -> Option<Z3Sig> {
    let mut cur_stack: Z3Int = 0.into();
    let mut peak_reach: Z3Int = 0.into();

    for instr in block {
        peak_reach = max(
            peak_reach,
            match instr.reach(known) {
                Ok(num) => (num as u64).into(),
                Err(e) => match e {
                    types::ResolveErr::FunctionUnresolved(name) => scc
                        .get(name)
                        .expect("Unresolved functions should belong to this same SCC")
                        .reach(),
                    types::ResolveErr::NotDeterminable => return None,
                    types::ResolveErr::IsQuit => unreachable!(),
                },
            } - cur_stack.clone(),
        );

        cur_stack += match instr.delta(known) {
            Ok(num) => num.into(),
            Err(e) => match e {
                types::ResolveErr::FunctionUnresolved(name) => scc
                    .get(name)
                    .expect("unresolved functions should belong to this same SCC")
                    .delta(),
                types::ResolveErr::NotDeterminable => return None,
                types::ResolveErr::IsQuit => Z3Int::fresh_const("quit"),
            },
        }
    }

    Some(Z3Sig {
        argc: peak_reach.clone(),
        retc: peak_reach + cur_stack,
    })
}

#[cfg(debug_assertions)]
// TODO: implement this
fn _debug_simulate_breaks(_func: &[types::Instr]) {}

fn get_block_breaks_v2(func: &[types::Instr]) -> BTreeSet<usize> {
    let mut breaks = BTreeSet::new();

    for (i, instr) in func.iter().enumerate() {
        dbg_println!("{} {:?}", i, instr);

        match instr {
            Instr::CFInstr(ControlFlowInstr::If) => {
                breaks.insert(i + 4);

                // end the block
                breaks.insert(i + 1);
            }
            Instr::CFInstr(ControlFlowInstr::Skip) => {
                // 2 cases:
                // if there is no BREAK at this position, and the previous value is a constant, then we are guaranteed to know how much we are going to jump by.
                // assuming that we have found all of the breaks up to this point. (TODO: PROVE THIS IS CORRECT)
                if !breaks.contains(&i)
                    && i > 0
                    && let Some(Instr::BBInstr(BasicBlockInstr::Literal(n))) = func.get(i - 1)
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
            Instr::BBInstr(_) => {}
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

pub(crate) fn analyze<'names, 'instrs>(
    graph: &petgraph::Graph<Vec<&'names str>, ()>,
    funcs: &HashMap<&str, &'instrs [types::Instr]>,
) -> HashMap<&'names str, BTreeMap<usize, Rc<Block>>> {
    let resolved = HashMap::new();

    let sort = petgraph::algo::toposort(graph, None)
        .expect("graph should not have any cycles. Make sure it is condensed");

    let signatures: HashMap<&str, ResolvedSig> = HashMap::new();

    for scc in sort {
        // set up Z3 solver for this scc
        let solver = z3::Solver::new();
        let scc: HashMap<_, _> = graph[scc]
            .iter()
            .map(|&func| {
                (
                    func,
                    Z3Sig {
                        argc: Z3Int::new_const(format!("{func}_argc")),
                        retc: Z3Int::new_const(format!("{func}_retc")),
                    },
                )
            })
            .collect();

        // let get: Vec<_> = Vec::new();

        for (&func_name, z3sig) in scc.iter() {
            let graph = create_graph(funcs.get(func_name).unwrap(), &signatures, &scc);
            dbg!(&graph);

            // FIXME: empty function
            let start = graph.get(&0).unwrap();

            let start_sig = &start.sig;

            // FIXME: fix
            let Some(q) = start_sig else { panic!() };

            solver.assert(z3sig.argc.eq(q.argc.clone()));

            build_same_return_count_constraint(start.clone(), &solver, z3sig).unwrap();
        }

        let out: Vec<_> = scc
            .into_iter()
            .map(|(_, sig)| (sig.argc, sig.retc))
            .collect();

        dbg!(&out);

        for sol in solver.solutions(out.as_slice(), true).take(20) {
            dbg!(sol);
        }
    }

    resolved
}

fn build_same_return_count_constraint(
    block: Rc<Block>,
    solver: &z3::Solver,
    func_sig: &Z3Sig,
) -> Option<()> {
    match &block.terminator {
        Terminator::Jump(next) => match next {
            Next::Trap => {} // no constraints from trap (like rust never type) // TODO: test : func quit ;
            Next::Terminate => {
                let sig = &block.sig;
                let Some(sig) = sig else { return None };

                solver.assert(sig.retc.eq(func_sig.retc.clone()));
            }
            Next::Block(next) => {
                build_same_return_count_constraint(next.clone(), solver, func_sig)?;
            }
        },
        Terminator::If { on_true, on_false } => todo!(),
        Terminator::Skip { targets } => todo!(),
    }

    Some(())
}

pub(crate) fn create_graph<'inst>(
    func: &'inst [types::Instr],
    known: &HashMap<&str, ResolvedSig>,
    scc: &HashMap<&str, Z3Sig>,
) -> BTreeMap<usize, Rc<Block>> {
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

    let get_next = |out: &BTreeMap<usize, Rc<Block>>, idx: usize| {
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

        let (code, terminator) = match last {
            Instr::CFInstr(cf) => match cf {
                ControlFlowInstr::If => (
                    (begin),
                    Terminator::If {
                        on_true: get_next(&out, start + code.len()),
                        on_false: get_next(&out, start + code.len() + 3),
                    },
                ),
                ControlFlowInstr::Skip
                    if let Some((Instr::BBInstr(BasicBlockInstr::Literal(amt)), begin2)) =
                        begin.split_last()
                        && let Ok(conv) = usize::try_from(*amt) =>
                {
                    (
                        (begin2),
                        Terminator::Jump(get_next(&out, start + code.len() + conv)),
                    )
                }
                ControlFlowInstr::Skip => (
                    (begin),
                    Terminator::Skip {
                        targets: ((start + code.len())..=func.len())
                            .map(|val| get_next(&out, val))
                            .collect(),
                    },
                ),
            },
            Instr::BBInstr(_) => ((code), Terminator::Jump(get_next(&out, start + code.len()))),
        };

        let code = to_basic_block_code(code)
            .expect("There should be no control flow statements in a basic block");

        let sig = get_delta_and_reach(&code, known, scc);

        let value = Block {
            code,
            sig,
            terminator,
        };

        out.insert(start, Rc::new(value));
    }

    out
}
