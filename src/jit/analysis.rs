use std::collections::{BTreeMap, BTreeSet};

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use cranelift::prelude::Signature;

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

use crate::types::{self, BasicBlockInstr, CRANELIFT_VALUE, ControlFlowInstr, Instr};

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
pub struct ResolvedSig {
    pub(crate) delta: Option<i64>, // None => never type (any delta)
    pub(crate) reach: usize,
}

impl ResolvedSig {
    pub fn argc(&self) -> usize {
        self.reach
    }

    pub fn retc(&self) -> usize {
        let amt = self.delta.map_or(0, |delta| (self.reach as i64) + delta);
        usize::try_from(amt).expect("By Clac++ theorem")
    }

    pub fn to_cranelift_signature(
        &self,
        call_conv: cranelift::prelude::isa::CallConv,
    ) -> Signature {
        Signature {
            params: vec![cranelift::prelude::AbiParam::new(CRANELIFT_VALUE); self.argc()],
            returns: vec![cranelift::prelude::AbiParam::new(CRANELIFT_VALUE); self.retc()],

            call_conv,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Z3Sig {
    delta: Z3Int,
    reach: Z3Int,
}

#[derive(Debug)]
// Each variant is the type of terminator
pub struct Block {
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

use z3::{Tactic, ast::Int as Z3Int};

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
                            println!("Could not analyze due to {} being not determinable. This should only happen because it relies on a function that cannot be resolved", name);
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
                        println!("Could not analyze due to {} being not determinable. This should only happen because it relies on a function that cannot be resolved", name);
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

fn solve_reach(model: &z3::Model, reach: &Z3Int) -> usize {
    model
        .eval(reach, false)
        .unwrap()
        .as_u64()
        .expect("Reach should be non-negative") as usize
}

fn solve_sig(
    model: &z3::Model,
    solver: &z3::Optimize,
    Z3Sig { delta, reach }: &Z3Sig,
) -> ResolvedSig {
    let mut delta_n: Option<i64> = model.eval(delta, false).and_then(|x| {
        // FIXME: this is a little suspicious, maybe add a check that this is actually unbounded?
        x.as_i64()
    });

    // TODO: This is kind of a hacky way of checking if something is unbounded. Look into a better way.
    if let Some(val) = delta_n {
        solver.push();
        solver.assert(delta.eq(val + 67));

        let unbounded = solver.check(&[]) == z3::SatResult::Sat;
        if unbounded {
            assert_eq!(
                val + 67,
                solver
                    .get_model()
                    .unwrap()
                    .eval(delta, false)
                    .unwrap()
                    .as_i64()
                    .unwrap()
            );

            delta_n = None;
            println!("{delta} is unbounded")
        }

        solver.pop();
    };

    let reach = solve_reach(model, reach);

    ResolvedSig {
        delta: delta_n,
        reach,
    }
}

pub struct AnalysisResult<'names> {
    /// CFG of functions
    pub code: HashMap<&'names str, BTreeMap<usize, Block>>,

    // resolved sig of the functions. The functions here are well behaved. As in, no matter the control flow path it takes to the end, it ultimately has the same stack delta.
    // TODO: prove theorem where in all well defined functions, all entrypoints to any given block must have the same stack delta
    pub resolved_sigs: HashMap<&'names str, ResolvedSig>,
}

pub(crate) fn analyze<'names, 'instrs>(
    graph: &petgraph::Graph<Vec<&'names str>, ()>,
    funcs: &HashMap<&str, &'instrs [types::Instr]>,
) -> AnalysisResult<'names> {
    let sort = petgraph::algo::toposort(graph, None)
        .expect("graph should not have any cycles. Make sure it is condensed");

    // functions with resolved signatures. In any specific SCC, all dependencies (any nodes that come before this scc in the topological sort) should have their signatures in here, given that they are resolvable.
    let mut signatures: HashMap<&str, ResolvedSig> = HashMap::new();

    // functions and code
    let mut out: HashMap<&str, BTreeMap<usize, Block>> = HashMap::new();

    // TODO: implement layered topological sort for parallelism
    'outer: for scc in sort {
        // set up Z3 solver for this scc
        // let pipeline = Tactic::new("simplify")
        //     .and_then(&Tactic::new("solve-eqs"))
        //     .and_then(&Tactic::new("smt"));

        // let solver = pipeline.optimize();
        let solver = z3::Optimize::new();

        let scc_original = &graph[scc];

        // create z3 signatures
        let scc_signatures: HashMap<_, _> = scc_original
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

        // create graphs
        let graphs: HashMap<_, _> = scc_original
            .iter()
            .map(|&func_name| {
                let func_graph =
                    // TODO: separate the z3 signature part
                    function_to_basic_blocks(funcs.get(func_name).unwrap(), &signatures, &scc_signatures);

                (func_name, func_graph)
            })
            .collect();

        // analyze graphs
        let analyzed: Option<HashMap<_, _>> = scc_original
            .iter()
            .map(|func_name| {
                let func_graph = &graphs[func_name];
                let (mut out_sigs, constraints) =
                    build_function_constraints_from_block_signatures(func_graph)?;

                let out_sig = out_sigs
                    .remove(&0)
                    .unwrap_or_else(|| {
                        // this should be empty function
                        assert_eq!(funcs[*func_name].len(), 0);

                        Some(Z3Sig {
                            delta: 0.into(),
                            reach: 0.into(),
                        })
                    })
                    .expect("Since Build completed");

                Some((*func_name, (out_sig, constraints)))
            })
            .collect();

        // dbg!(&analyzed);

        out.extend(graphs.into_iter().map(|(func_name, func_graph)| {
            (
                func_name,
                func_graph
                    .into_iter()
                    .map(|(pos, (block, _))| (pos, block))
                    .collect(),
            )
        }));

        // there was a function in thie SCC that could not be analyzed
        let Some(analyzed) = analyzed else {
            println!("ANALYSIS FAILED. Abandoning SCC {:?}", scc_signatures);

            continue 'outer;
        };

        analyzed
            .into_iter()
            .for_each(|(func_name, (out_sig, assertions))| {
                assertions.iter().for_each(|bool| {
                    solver.assert(bool);
                });

                let z3sig = &scc_signatures[func_name];

                solver.assert(z3sig.delta.eq(out_sig.delta));
                solver.assert(z3sig.reach.eq(out_sig.reach));

                solver.minimize(&z3sig.reach);
            });

        // println!("solving scc = {:?}", scc);
        let z3::SatResult::Sat = solver.check(&[]) else {
            println!("z3 COULD NOT SOLVE SCC: {:?}", scc_signatures);
            continue 'outer;
        };

        let model = solver.get_model().unwrap();

        // add to known signatures
        signatures.extend(scc_signatures.iter().map(|(func_name, z3sig)| {
            let var_name = (*func_name, solve_sig(&model, &solver, z3sig));
            // println!("Resolved {var_name:?}");

            var_name
        }));
    }

    println!(
        "Resolved {}/{} Signatures: {:?}",
        signatures.len(),
        funcs.len(),
        signatures
    );

    AnalysisResult {
        code: out,
        resolved_sigs: signatures,
    }
}

fn build_function_constraints_from_block_signatures(
    blocks: &BTreeMap<usize, (Block, Option<Z3Sig>)>,
    // ) -> Option<HashSet<z3::ast::Bool>> {
) -> Option<(HashMap<usize, Option<Z3Sig>>, HashSet<z3::ast::Bool>)> {
    if blocks.is_empty() {
        return Some((HashMap::new(), HashSet::new()));
    }

    fn build_path_signatures_starting_from_here<'a>(
        start: usize,
        blocks: &BTreeMap<usize, (Block, Option<Z3Sig>)>,
        resolved: &'a mut HashMap<usize, Option<Z3Sig>>,
        assertions: &mut HashSet<z3::ast::Bool>,
    ) -> Option<&'a Z3Sig> {
        if resolved.contains_key(&start) {
            return resolved.get(&start).unwrap().as_ref();
        }

        let old_start = start;
        let (start, start_sig) = &blocks[&start];
        let Some(my_sig) = start_sig else {
            // cannot resolve this path due to this block being unresolvable
            debug_assert_eq!(resolved.contains_key(&old_start), false);

            return resolved.entry(old_start).or_insert(None).as_ref();
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
                    let next_sig = build_path_signatures_starting_from_here(
                        next, blocks, resolved, assertions,
                    )?;

                    Some(Z3Sig {
                        delta: my_delta + next_sig.delta.clone(),
                        reach: next_sig.reach.clone() - my_delta,
                    })
                }
            }
        };

        let to_ins = match &start.terminator {
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
                    .fold(my_reach.clone(), |a: Z3Int, b| max(a, b.reach.clone()));

                Some(Z3Sig {
                    delta: resolved[0].delta.clone(),
                    reach: max_subpath_reach,
                })
            }
        };

        return resolved.entry(old_start).or_insert(to_ins).as_ref();
    }

    let mut assertions = HashSet::new();
    let mut res = HashMap::with_capacity(blocks.len());

    let _build = build_path_signatures_starting_from_here(0, blocks, &mut res, &mut assertions)?;

    Some((res, assertions))
}

pub(crate) fn function_to_basic_blocks<'inst>(
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

    dbg_println!("pre processed basic blocks = {:?}", basic_blocks);

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
