use std::collections::{BTreeMap, BTreeSet};

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};

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
    Block(usize),
}

#[derive(Debug)]
/// A resolved function signature
pub(crate) struct ResolvedSig {
    pub(crate) delta: Option<i64>, // None => never type (any delta)
    pub(crate) reach: usize,
}

#[derive(Debug)]
pub(crate) struct Z3Sig {
    delta: Z3Int,
    reach: Z3Int,
}

#[derive(Debug)]
// Each variant is the type of terminator
pub(crate) struct Block {
    // FIXME: this could be Cow
    pub(crate) code: Vec<BasicBlockInstr>,
    pub(crate) terminator: Terminator,
}

fn resolve_drops_and_picks<'a>(block: &'a [Instr]) -> Vec<Instr> {
    let mut res = Vec::new();

    for (i, instr) in block.iter().enumerate() {
        use Instr::*;
        let out = match instr {
            // resolve drop range
            BBInstr(BasicBlockInstr::BadDropRange)
                if i >= 2
                    && let &[
                        Instr::BBInstr(BasicBlockInstr::Literal(start)),
                        Instr::BBInstr(BasicBlockInstr::Literal(amt)),
                    ] = &block[i - 2..i]
                    && let Ok(start) = start.try_into()
                    && let Ok(amt) = amt.try_into() =>
            {
                let BBInstr(BasicBlockInstr::Literal(x)) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, amt);

                let BBInstr(BasicBlockInstr::Literal(x)) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, start);

                assert!(start >= amt);

                BBInstr(BasicBlockInstr::ResolvedDropRange { start, amt })
            }
            // resolve pick
            BBInstr(BasicBlockInstr::BadPick)
                if i >= 1
                    && let Instr::BBInstr(BasicBlockInstr::Literal(n)) = block[i - 1]
                    && let Ok(n) = usize::try_from(n) =>
            {
                let BBInstr(BasicBlockInstr::Literal(x)) = res.pop().unwrap() else {
                    unreachable!()
                };
                assert_eq!(x as usize, n);

                assert!(n >= 1);
                BBInstr(BasicBlockInstr::ResolvedPick(n))
            }
            // FIXME: this should be Cow
            x => x.clone(),
        };

        res.push(out);
    }

    res
}

use z3::ast::Int as Z3Int;

fn max(a: Z3Int, b: Z3Int) -> Z3Int {
    let cond = a.gt(&b);
    cond.ite(&a, &b)
}

fn get_delta_and_reach(
    block: &[Instr],
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
                        .or_else(|| {
                            println!("Could not build due to {} being not determinable. This should only happen because it relies on a function that cannot be resolved", name);
                            return None;
                        })?
                        .reach
                        .clone(),
                    // .expect("Unresolved functions should belong to this same SCC")
                    // .reach(),
                    types::ResolveErr::NotDeterminable => return None,
                    types::ResolveErr::Anything => unreachable!(),
                },
            } - cur_stack.clone(),
        );

        cur_stack += match instr.delta(known) {
            Ok(num) => num.into(),
            Err(e) => match e {
                types::ResolveErr::FunctionUnresolved(name) => scc
                    .get(name)
                    .or_else(|| {
                        println!("Could not build due to {} being not determinable. This should only happen because it relies on a function that cannot be resolved", name);
                        return None;
                    })?
                    .delta
                    .clone(),
                // .expect("unresolved functions should belong to this same SCC")
                // .delta(),
                types::ResolveErr::NotDeterminable => return None,
                types::ResolveErr::Anything => Z3Int::fresh_const("anything"),
            },
        }
    }

    Some(Z3Sig {
        delta: cur_stack,
        reach: peak_reach,
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
) -> HashMap<
    &'names str, // function name
    (
        BTreeMap<usize, (Block, Option<ResolvedSig>)>, // function code, with blocks that may have resolved sigs
        Option<ResolvedSig>,                           // resolved sig of the function
    ),
> {
    // let resolved = HashMap::new();

    let sort = petgraph::algo::toposort(graph, None)
        .expect("graph should not have any cycles. Make sure it is condensed");

    // functions with resolved signatures
    let mut signatures: HashMap<&str, ResolvedSig> = HashMap::new();

    'outer: for scc in sort {
        // set up Z3 solver for this scc
        let solver = z3::Solver::new();
        let scc: HashMap<_, _> = graph[scc]
            .iter()
            .map(|&func| {
                (
                    func,
                    Z3Sig {
                        delta: Z3Int::new_const(format!("{func}_delta")),
                        reach: Z3Int::new_const(format!("{func}_reach")),
                    },
                )
            })
            .collect();

        // dbg!(&scc);

        for (&func_name, func_sig) in scc.iter() {
            let inner = || -> Option<()> {
                let func_graph = create_graph(funcs.get(func_name).unwrap(), &signatures, &scc);
                // println!("{func_name}.func_graph = {func_graph:?}");

                let (out_sig, constraints) =
                    build_function_constraints_from_block_signatures(&func_graph)?;

                // print!("Constraints for {func_name} = {constraints:?} | out_sig = {out_sig:?}\n");

                constraints.into_iter().for_each(|bool| {
                    solver.assert(bool);
                });

                solver.assert(func_sig.delta.eq(out_sig.delta));
                solver.assert(func_sig.reach.eq(out_sig.reach));

                Some(())
            };

            let Some(()) = inner() else {
                println!("RESOLVE FAILED: {func_name}. Abandoning SCC {:?}", scc);
                continue 'outer;
            };
        }

        // println!("solving scc = {:?}", scc);

        // everything in this SCC is resolvable
        match solver.check() {
            z3::SatResult::Sat => {
                let model = solver.get_model().unwrap();

                let solve_sig = |Z3Sig { delta, reach }| {
                    let mut delta_n: Option<i64> = model.eval(&delta, false).and_then(|x| {
                        // dbg!(&x);
                        // FIXME: this is a little suspicious, maybe add a check that this is actually unbounded?
                        x.as_i64()
                    });

                    if let Some(val) = delta_n {
                        solver.push();
                        solver.assert(delta.eq(val + 67));

                        let unbounded = solver.check() == z3::SatResult::Sat;
                        if unbounded {
                            assert_eq!(
                                val + 67,
                                solver
                                    .get_model()
                                    .unwrap()
                                    .eval(&delta, false)
                                    .unwrap()
                                    .as_i64()
                                    .unwrap()
                            );

                            delta_n = None;
                            println!("{delta} is unbounded")
                        }

                        solver.pop(1);
                    };

                    let reach = model
                        .eval(&reach, false)
                        .unwrap()
                        .as_u64()
                        .expect("Reach should be non-negative")
                        as usize;

                    ResolvedSig {
                        delta: delta_n,
                        reach,
                    }
                };

                signatures.extend(scc.into_iter().map(|(func_name, sig)| {
                    let var_name = (func_name, solve_sig(sig));
                    println!("Resolved {var_name:?}");
                    var_name
                }));

                // println!("SAT! signatures = {:?}", signatures);
            }
            z3::SatResult::Unsat | z3::SatResult::Unknown => {
                println!("COULD NOT SOLVE SCC: {:?}", scc);
                // todo!();
            }
        }
    }

    println!(
        "Resolved {}/{} Signatures: {:?}",
        signatures.len(),
        funcs.len(),
        signatures
    );

    // dbg!(signatures);

    todo!()
}

fn build_function_constraints_from_block_signatures(
    blocks: &BTreeMap<usize, (Block, Option<Z3Sig>)>,
    // ) -> Option<HashSet<z3::ast::Bool>> {
) -> Option<(Z3Sig, HashSet<z3::ast::Bool>)> {
    // let mut out: HashSet<_> = HashSet::new();
    // let mut visited: HashSet<usize> = HashSet::new();
    // let mut to_visit: Vec<usize> = vec![0];

    fn resolve_path(
        start: usize,
        blocks: &BTreeMap<usize, (Block, Option<Z3Sig>)>,
        assertions: &mut HashSet<z3::ast::Bool>,
    ) -> Option<Z3Sig> {
        let (start, start_sig) = &blocks[&start];
        let Some(my_sig) = start_sig else {
            return None;
        };

        let my_delta = &my_sig.delta;
        let my_reach = &my_sig.reach;

        // get delta and reach relative to start,  if we were to go down this path
        let mut resolve_next = |next: &Next| {
            match next {
                Next::Trap => Some(Z3Sig {
                    delta: Z3Int::fresh_const("unconstrained_trap"), // trap -> delta could be anything
                    reach: my_reach.clone(),
                }),

                Next::Terminate => Some(Z3Sig {
                    delta: my_delta.clone(),
                    reach: my_reach.clone(),
                }), // my delta and reach

                &Next::Block(next) => {
                    let next_sig = resolve_path(next, blocks, assertions)?;

                    // let lol = Solver::new();
                    // for assertion in assertions.iter() {
                    //     lol.assert(assertion);
                    // }
                    // assert_eq!(lol.check(), SatResult::Sat);

                    // println!("Going down path starting at {next}:");
                    // dbg!(lol.get_model().unwrap().eval(&next_sig.delta, false));
                    // println!("Going down path starting at {next} ==> {next_sig:?}");

                    Some(Z3Sig {
                        delta: my_delta + next_sig.delta,
                        reach: next_sig.reach - my_delta,
                    })
                }
            }
        };

        match &start.terminator {
            Terminator::Jump(next) => {
                let resolve_next1 = resolve_next(next)?;

                Some(Z3Sig {
                    delta: resolve_next1.delta,
                    reach: max(my_reach.clone(), resolve_next1.reach),
                })
            }
            Terminator::If { on_true, on_false } => {
                let on_true = resolve_next(on_true)?;
                let on_false = resolve_next(on_false)?;

                assertions.insert(on_true.delta.eq(on_false.delta));

                Some(Z3Sig {
                    delta: on_true.delta,
                    reach: max(my_reach.clone(), max(on_true.reach, on_false.reach)),
                })
            }
            Terminator::Skip { targets } => {
                let resolved: Option<Vec<Z3Sig>> =
                    targets.iter().map(|x| resolve_next(x)).collect();

                // We can only resolve this one if all its subpaths can be resolved
                let resolved: Vec<Z3Sig> = resolved?;

                // all the path deltas should be equal.
                for sig in resolved.iter() {
                    assertions.insert(sig.delta.eq(&resolved[0].delta));
                }

                let max_subpath_reach = resolved
                    .iter()
                    .fold(0.into(), |a: Z3Int, b| max(a, b.reach.clone()));

                Some(Z3Sig {
                    delta: resolved[0].delta.clone(),
                    reach: max(my_reach.clone(), max_subpath_reach),
                })
            }
        }
    }

    let mut assertions = HashSet::new();
    let ret = resolve_path(0, blocks, &mut assertions)?;

    Some((ret, assertions))
}

pub(crate) fn create_graph<'inst>(
    func: &'inst [types::Instr],
    known: &HashMap<&str, ResolvedSig>,
    scc: &HashMap<&str, Z3Sig>,
) -> BTreeMap<usize, (Block, Option<Z3Sig>)> {
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

    let mut out: BTreeMap<_, _> = BTreeMap::new();

    for (start_unresolved, unresolved) in basic_blocks.into_iter().rev() {
        // println!("{code:?}.sig = {:?}", sig);

        let get_next = |idx_unresolved: usize| {
            if idx_unresolved > func.len() {
                return Next::Trap;
            } else if idx_unresolved == func.len() {
                return Next::Terminate;
            }

            assert!(idx_unresolved < func.len());

            // NOTE: it is important that order of iteration is reversed, we are exploiting the fact that it is impossible for a clac program to jump backward
            assert!(out.contains_key(&idx_unresolved));
            return Next::Block(idx_unresolved);
        };

        // NOTE: it is very important to resolve first before we try finding deltas
        let resolved = resolve_drops_and_picks(unresolved);

        let sig = get_delta_and_reach(&resolved, known, scc);

        let (last, body) = resolved.split_last().expect("basic_block.len() >= 1");

        let (new_slice, terminator) = match last {
            Instr::CFInstr(cf) => match cf {
                ControlFlowInstr::If => (
                    body,
                    Terminator::If {
                        on_true: get_next(start_unresolved + unresolved.len()),
                        on_false: get_next(start_unresolved + unresolved.len() + 3),
                    },
                ),
                ControlFlowInstr::Skip
                    if let Some((Instr::BBInstr(BasicBlockInstr::Literal(amt)), body2)) =
                        body.split_last()
                        && let Ok(conv) = usize::try_from(*amt) =>
                {
                    (
                        body2,
                        Terminator::Jump(get_next(start_unresolved + unresolved.len() + conv)),
                    )
                }
                ControlFlowInstr::Skip => (
                    body,
                    Terminator::Skip {
                        targets: ((start_unresolved + unresolved.len())..=func.len())
                            .map(|val| get_next(val))
                            .collect(),
                    },
                ),
            },
            Instr::BBInstr(_) => (
                resolved.as_slice(),
                Terminator::Jump(get_next(start_unresolved + unresolved.len())),
            ),
        };

        // TODO: improve this (don't clone)
        let new_slice = new_slice
            .iter()
            .map(|x| {
                BasicBlockInstr::try_from(x.clone())
                    .expect("There should be no control flow statements in a basic block)")
            })
            .collect();

        let value = Block {
            code: new_slice,
            terminator,
        };

        out.insert(start_unresolved, (value, sig));
    }

    out
}
