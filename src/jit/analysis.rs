use std::collections::{BTreeMap, BTreeSet};

use ahash::{HashMap, HashMapExt};
use cranelift::prelude::Signature;

use crate::types::{self, BasicBlockInstr, CRANELIFT_VALUE, ControlFlowInstr, Instr};

use std::cmp::max;

macro_rules! dbg_println {
    ($($args:tt)*) => {
        #[cfg(feature = "debug")]
        println!($($args)*)
    };
}

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
    pub(crate) delta: Option<isize>, // None => never type (any delta)
    pub(crate) reach: usize,
}

impl ResolvedSig {
    pub fn argc(&self) -> usize {
        self.reach
    }

    pub fn retc(&self) -> usize {
        let amt = self.delta.map_or(0, |delta| (self.reach as isize) + delta);
        amt.try_into().expect("By Clac++ theorem")
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
// Each variant is the type of terminator
pub struct Block {
    // FIXME: this could be Cow
    pub(crate) code: Vec<BasicBlockInstr>,
    pub(crate) terminator: Terminator,
}

pub struct AnalysisResult<'names> {
    /// CFG of functions
    pub code: HashMap<&'names str, BTreeMap<usize, Block>>,

    // resolved sig of the functions. The functions here are well behaved. As in, no matter the control flow path it takes to the end, it ultimately has the same stack delta.
    // TODO: prove theorem where in all well defined functions, all entrypoints to any given block must have the same stack delta
    pub resolved_sigs: HashMap<&'names str, ResolvedSig>,
}

pub(crate) fn analyze<'names>(
    sccs_graph: &petgraph::Graph<Vec<&'names str>, ()>,
    funcs: &HashMap<&'names str, &[types::Instr]>,
) -> AnalysisResult<'names> {
    // Split functions into blocks
    let all_blocks: HashMap<&str, BTreeMap<usize, Block>> = funcs
        .iter()
        .map(|(&func_name, func_instrs)| (func_name, raw_func_instrs_to_blocks(func_instrs)))
        .collect();

    // Toposort SCCs
    // TODO: implement layered topological sort for parallelism
    let sccs_in_order = petgraph::algo::toposort(sccs_graph, None)
        .expect("Cycle should have been removed by graph condensation");

    // --- FIND DELTAS AND REACHES ---

    let mut all_deltas = HashMap::<&str, Delta>::new();
    let mut all_reaches = HashMap::<&str, Reach>::new();

    for scc in sccs_in_order {
        let scc_func_names = sccs_graph[scc].as_slice();

        // --- Find deltas ---

        // Initially guess that all of the functions are Never
        let mut delta_guesses: Vec<(&str, Delta)> = scc_func_names
            .iter()
            .map(|&name| (name, Delta::Never))
            .collect();
        // Repeatedly re-guess
        loop {
            delta_guesses.iter().for_each(|(name, d)| {
                all_deltas.insert(name, d.clone());
            });
            let new_delta_guesses: Vec<(&str, Delta)> = scc_func_names
                .iter()
                .map(|&name| {
                    let code = all_blocks
                        .get(name)
                        .expect("Function in SCC should have its blocks known");
                    (name, find_func_delta(code, &all_deltas))
                })
                .collect();
            if new_delta_guesses == delta_guesses {
                break;
            }
            delta_guesses = new_delta_guesses;
        }

        // --- Throw out functions that are known to be not well-behaved (give them dummy/default reach, it shouldn't matter what) ---
        let funcs_with_well_behaved_deltas: Vec<&str> = scc_func_names
            .iter()
            .map(|&name| name)
            .filter(|name| {
                match all_deltas
                    .get(name)
                    .expect("Function in SCC should have had its delta analyzed")
                {
                    Delta::NotWellBehaved => {
                        all_reaches.insert(name, Reach::default()); // Dummy value (must be inserted)
                        false
                    }
                    _ => true,
                }
            })
            .collect();

        // --- Do infinite-reach detection on the remaining reaches ---
        // FIXME!!!: MAKE IT SO THAT WE CAN USE ACTUAL ISIZE EDGES INSTEAD OF F64 EDGES
        // (petgraph's find_negative_cycle requires f64 edges)
        let mut graph: petgraph::Graph<&str, f64> = petgraph::Graph::new();
        let nodes: HashMap<&str, _> = funcs_with_well_behaved_deltas
            .iter()
            .map(|&name| (name, graph.add_node(name)))
            .collect();
        for caller_name in funcs_with_well_behaved_deltas {
            for (callee_name, call_delta) in find_func_calls_with_deltas(
                all_blocks
                    .get(caller_name)
                    .expect("Name should refer to function in funcs"),
                &all_deltas,
            ) {
                graph.add_edge(
                    *nodes.get(caller_name).expect(
                        "Caller should have been included as a function with well-behaved delta",
                    ),
                    *nodes.get(callee_name).expect(
                        "Callee should have been included as a function with well-behaved delta",
                    ),
                    call_delta as f64,
                );
            }
        }
        let funcs_with_well_behaved_deltas_and_bounded_reaches: Vec<&str> = nodes
            .iter()
            .filter_map(|(&name, &index)| {
                if petgraph::algo::find_negative_cycle(&graph, index).is_some() {
                    // If negative cycle, then its reach is unbounded,
                    // and we don't include it in the filtered list
                    all_reaches.insert(name, Reach::Unbounded);
                    None
                } else {
                    // If no negative cycle, we continue to analyze it
                    // in the next step
                    Some(name)
                }
            })
            .collect();

        // --- Repeatedly guess reaches for those that are neither not-well-behaved-delta nor infinite-reach ---
        let mut reach_guesses: Vec<(&str, Reach)> =
            funcs_with_well_behaved_deltas_and_bounded_reaches
                .iter()
                .map(|&name| (name, Reach::Num(0)))
                .collect();
        loop {
            reach_guesses.iter().for_each(|(name, r)| {
                all_reaches.insert(name, r.clone());
            });
            let new_reach_guesses: Vec<(&str, Reach)> =
                funcs_with_well_behaved_deltas_and_bounded_reaches
                    .iter()
                    .map(|&name| {
                        let code = all_blocks
                            .get(name)
                            .expect("Function in SCC should have its blocks known");
                        (name, find_func_reach(code, &all_deltas, &all_reaches))
                    })
                    .collect();
            if new_reach_guesses == reach_guesses {
                break;
            }
            reach_guesses = new_reach_guesses;
        }
    }

    // Combine Deltas and Reaches into ResolvedSigs
    let all_sigs: HashMap<&str, ResolvedSig> = funcs
        .iter()
        .filter_map(|(&func_name, _)| {
            delta_and_reach_to_resolved_sig(
                all_deltas
                    .get(func_name)
                    .expect("Function should have been analyzed for delta"),
                all_reaches
                    .get(func_name)
                    .expect("Function should have been analyzed for reach"),
            )
            .map(|sig| (func_name, sig))
        })
        .collect();

    println!("--- Signatures Found ---");
    println!("{:#?}", all_sigs);

    // Return result
    AnalysisResult {
        code: all_blocks,
        resolved_sigs: all_sigs,
    }
}

fn raw_func_instrs_to_blocks(func_code: &[Instr]) -> BTreeMap<usize, Block> {
    // Get breaks
    let mut breaks: BTreeSet<usize> = get_block_breaks_v2(func_code);
    dbg_println!("breaks = {:?}", breaks);

    // Divide according to breaks
    breaks.insert(func_code.len()); // Put break at end of function
    let mut blocks: Vec<(usize, &[Instr])> = Vec::new();
    let mut prev_br: usize = 0;
    for mut curr_br in breaks {
        if prev_br == func_code.len() {
            break;
        }
        curr_br = std::cmp::min(curr_br, func_code.len());
        blocks.push((prev_br, &func_code[prev_br..curr_br]));
        prev_br = curr_br;
    }

    dbg_println!("basic blocks before processing = {:?}", unprocessed);

    // Get terminators (must be done BEFORE resolving drops and picks)
    let blocks: Vec<(usize, (&[Instr], Terminator))> = blocks
        .into_iter()
        .map(|(block_start, block_code)| {
            (
                block_start,
                extract_terminator(block_start, block_code, func_code.len()),
            )
        })
        .collect();

    // Resolve drops and picks
    let blocks: Vec<(usize, (Vec<Instr>, Terminator))> = blocks
        .into_iter()
        .map(|(block_start, (block_code, terminator))| {
            (
                block_start,
                (resolve_drops_and_picks(block_code), terminator),
            )
        })
        .collect();

    // Finalize blocks by coercing instructions to basic block instructions and collecting blocks in a BTreeMap
    let blocks: BTreeMap<usize, Block> = blocks
        .into_iter()
        .map(|(block_start, (instrs, terminator))| {
            (
                block_start,
                Block {
                    code: instrs
                        .into_iter()
                        .map(|raw_instr| {
                            raw_instr.try_into().expect(
                                "Block should only contain basic block instructions at this point",
                            )
                        })
                        .collect(),
                    terminator,
                },
            )
        })
        .collect();

    blocks
}

// TODO: This function could theoretically suffer from addition overflow/wraparound in extreme cases?
fn get_block_breaks_v2(func_code: &[Instr]) -> BTreeSet<usize> {
    use {BasicBlockInstr::*, ControlFlowInstr::*, Instr::*};
    let mut breaks = BTreeSet::<usize>::new();

    // Must go forward (takes advantage of Clac control flow)
    for (i, instr) in func_code.iter().enumerate() {
        dbg_println!("{} {:?}", i, instr);
        match instr {
            CFInstr(If) => {
                breaks.insert(i + 1);
                breaks.insert(i + 4);
            }
            // 2 cases for skips:
            // if there is no BREAK at this position, and the previous value is a constant, then we are guaranteed to know how much we are going to jump by.
            // assuming that we have found all of the breaks up to this point. (TODO: PROVE THIS IS CORRECT)
            CFInstr(Skip)
                if !breaks.contains(&i)
                    && i > 0
                    && let Some(BBInstr(Literal(n))) = func_code.get(i - 1)
                    && let Ok(n) = usize::try_from(*n) =>
            {
                breaks.insert(i + 1);
                breaks.insert(i + 1 + n);
            }
            CFInstr(Skip) => {
                breaks.extend((i + 1)..=func_code.len());
            }
            BBInstr(_) => (),
        }
    }

    breaks
}

fn extract_terminator(
    block_start: usize,
    block_code: &[Instr],
    func_length: usize,
) -> (&[Instr], Terminator) {
    use {BasicBlockInstr::*, ControlFlowInstr::*, Instr::*, std::cmp::Ordering::*};
    let get_next = |position: usize| match position.cmp(&func_length) {
        Less => Next::Block(position),
        Equal => Next::Terminate,
        Greater => Next::Trap,
    };
    match block_code {
        [body @ .., CFInstr(If)] => (
            body,
            Terminator::If {
                on_true: get_next(block_start + block_code.len()),
                on_false: get_next(block_start + block_code.len() + 3),
            },
        ),
        [body @ .., BBInstr(Literal(n)), CFInstr(Skip)] if let Ok(n) = usize::try_from(*n) => (
            body,
            Terminator::Jump(get_next(block_start + block_code.len() + n)),
        ),
        [body @ .., CFInstr(Skip)] => (
            body,
            Terminator::Skip {
                targets: ((block_start + block_code.len())..=func_length)
                    .map(|target| get_next(target))
                    .collect(),
            },
        ),
        _ => (
            block_code,
            Terminator::Jump(get_next(block_start + block_code.len())),
        ),
    }
}

// TODO: Should invalid arguments cause a panic? Should 0 0 drop_range be disallowed?
fn resolve_drops_and_picks(mut block_code: &[Instr]) -> Vec<Instr> {
    use {BasicBlockInstr::*, Instr::*};
    let mut result = Vec::<Instr>::new();
    loop {
        let (instr_to_push, rest) = match block_code {
            [
                BBInstr(Literal(start)),
                BBInstr(Literal(amt)),
                BBInstr(BadDropRange),
                rest @ ..,
            ] if let Ok(start) = (*start).try_into()
                && let Ok(amt) = (*amt).try_into()
                && start >= amt =>
            {
                (BBInstr(ResolvedDropRange { start, amt }), rest)
            }
            [BBInstr(Literal(n)), BBInstr(BadPick), rest @ ..]
                if let Ok(n) = (*n).try_into()
                    && n >= 1 =>
            {
                (BBInstr(ResolvedPick(n)), rest)
            }
            // FIXME: This should be Cow
            [instruction, rest @ ..] => (instruction.clone(), rest),
            [] => break,
        };
        result.push(instr_to_push);
        block_code = rest;
    }
    result
}

#[derive(PartialEq, Clone, Debug)]
pub(crate) enum Delta {
    Num(isize),
    Never,
    NotWellBehaved,
}

fn combine_sequential_deltas(d1: Delta, d2: Delta) -> Delta {
    use Delta::*;
    match (d1, d2) {
        (Never, _) => Never, // What comes after doesn't matter due to trap
        (NotWellBehaved, _) => NotWellBehaved, // Carrying over stack could fail, even if the next operation is Never
        (Num(_), Never) => Never,
        (Num(_), NotWellBehaved) => NotWellBehaved,
        (Num(d1), Num(d2)) => Num(d1 + d2),
    }
}

fn combine_branching_deltas(d1: Delta, d2: Delta) -> Delta {
    use Delta::*;
    match (d1, d2) {
        (Never, d) | (d, Never) => d,
        (Num(d1), Num(d2)) if d1 == d2 => Num(d1),
        _ => NotWellBehaved,
    }
}

fn find_func_delta(blocks: &BTreeMap<usize, Block>, known: &HashMap<&str, Delta>) -> Delta {
    // A given block's associated path delta is the delta of starting with that block and going to the end of the function
    let mut path_deltas = BTreeMap::<usize, Delta>::new();

    // for loop must be backward (takes advantage of Clac control flow)
    for (&curr_pos, curr_block) in blocks.iter().rev() {
        // Add together body of current block
        let block_body_delta = curr_block
            .code
            .iter()
            .map(|basic_block_instr| basic_block_instr.delta(&known))
            .fold(Delta::Num(0), combine_sequential_deltas);

        // Lambda to convert Next component of Terminator to Delta
        let delta_from_next = |next: &Next| -> Delta {
            match next {
                Next::Block(next_pos) => path_deltas
                    .get(next_pos)
                    .expect("Referenced block's delta should have already been analyzed")
                    .clone(),
                Next::Terminate => Delta::Num(0),
                Next::Trap => Delta::Never,
            }
        };

        // Add on terminator
        let curr_path_delta = combine_sequential_deltas(
            block_body_delta,
            match &curr_block.terminator {
                Terminator::Jump(next) => delta_from_next(next),
                Terminator::If { on_true, on_false } => combine_sequential_deltas(
                    Delta::Num(-1),
                    combine_branching_deltas(delta_from_next(on_true), delta_from_next(on_false)),
                ),
                Terminator::Skip { targets } => combine_sequential_deltas(
                    Delta::Num(-1),
                    targets
                        .iter()
                        .map(delta_from_next)
                        .fold(delta_from_next(&Next::Trap), combine_branching_deltas),
                ),
            },
        );

        path_deltas.insert(curr_pos, curr_path_delta);
    }
    // Default delta for empty function is 0
    path_deltas.get(&0).map_or(Delta::Num(0), Clone::clone)
}

#[derive(PartialEq, Clone, Debug, Default)]
pub(crate) enum Reach {
    Num(usize),
    #[default]
    Unbounded,
}

fn combine_sequential_reaches((r1, d1): (Reach, Delta), r2: Reach) -> Reach {
    match (r1, d1, r2) {
        (Reach::Num(r1), Delta::Num(d1), Reach::Num(r2)) => Reach::Num(max(
            r1,
            r2.checked_sub_signed(d1).unwrap_or_else(|| {
                if d1 >= 0 {
                    0
                } else {
                    panic!("Overflow during reach calculation") // TODO Is this panic a problem when we are analyzing post-Never stuff?
                }
            }),
        )),
        (Reach::Unbounded, Delta::Num(_), _) | (_, Delta::Num(_), Reach::Unbounded) => {
            Reach::Unbounded
        }
        (r1, Delta::Never, _) => r1,
        (_, Delta::NotWellBehaved, _) => Reach::default(), // Dummy value (should end up being thrown out later anyway)
    }
}

fn combine_branching_reaches(r1: Reach, r2: Reach) -> Reach {
    use Reach::*;
    match (r1, r2) {
        (Unbounded, _) | (_, Unbounded) => Unbounded,
        (Num(r1), Num(r2)) => Num(max(r1, r2)),
    }
}

// SHOULD ONLY BE CALLED ON FUNCTIONS WITH WELL-BEHAVED DELTAS
fn find_func_reach(
    blocks: &BTreeMap<usize, Block>,
    known_deltas: &HashMap<&str, Delta>,
    known_reaches: &HashMap<&str, Reach>,
) -> Reach {
    let mut path_reaches = BTreeMap::<usize, Reach>::new();

    for (&curr_pos, curr_block) in blocks.iter().rev() {
        let reach_from_next = |next: &Next| -> Reach {
            match next {
                Next::Block(next_pos) => path_reaches
                    .get(next_pos)
                    .expect("Referenced block's reach should have already been analyzed")
                    .clone(),
                Next::Terminate => Reach::Num(0),
                Next::Trap => Reach::Num(0),
            }
        };

        let terminator_reach = match &curr_block.terminator {
            Terminator::Jump(next) => reach_from_next(next),
            Terminator::If { on_true, on_false } => combine_sequential_reaches(
                (Reach::Num(1), Delta::Num(-1)),
                combine_branching_reaches(reach_from_next(on_true), reach_from_next(on_false)),
            ),
            Terminator::Skip { targets } => combine_sequential_reaches(
                (Reach::Num(1), Delta::Num(-1)),
                targets
                    .iter()
                    .map(reach_from_next)
                    .fold(reach_from_next(&Next::Trap), combine_branching_reaches),
            ),
        };

        let curr_path_reach = curr_block
            .code
            .iter()
            .map(|basic_block_instr| {
                (
                    basic_block_instr.reach(&known_reaches),
                    basic_block_instr.delta(&known_deltas),
                )
            })
            .rev()
            .fold(terminator_reach, |r, l| combine_sequential_reaches(l, r));

        path_reaches.insert(curr_pos, curr_path_reach);
    }

    path_reaches.get(&0).map_or(Reach::Num(0), Clone::clone)
}

fn basic_block_instr_to_calls_with_deltas<'a>(instr: &'a BasicBlockInstr) -> Vec<(&'a str, isize)> {
    match instr {
        BasicBlockInstr::FunctionCall(func_name_string) => vec![(func_name_string.as_str(), 0)],
        _ => vec![],
    }
}

// TODO: Eliminate unncessary duplicate edges

fn combine_sequential_calls_with_deltas<'a>(
    (c1, d1): (Vec<(&'a str, isize)>, Delta),
    c2: Vec<(&'a str, isize)>,
) -> Vec<(&'a str, isize)> {
    match d1 {
        Delta::Num(d1) => {
            let mut result = c1;
            result.extend(
                c2.iter()
                    .map(|&(name, d)| (name, d1 + d))
                    .collect::<Vec<_>>(),
            );
            result
        }
        Delta::Never => c1,
        Delta::NotWellBehaved => Vec::default(), // Dummy value (non-well-behaved behavior should not be reachable if we analyze a well-behaved function)
    }
}

fn combine_branching_calls_with_deltas<'a>(
    c1: Vec<(&'a str, isize)>,
    c2: Vec<(&'a str, isize)>,
) -> Vec<(&'a str, isize)> {
    let mut result = c1;
    result.extend(c2);
    result
}

// TODO: Make the efficiency of this function (and others) better
fn find_func_calls_with_deltas<'a>(
    blocks: &'a BTreeMap<usize, Block>,
    known_deltas: &HashMap<&str, Delta>,
) -> Vec<(&'a str, isize)> {
    let mut path_calls_with_deltas = BTreeMap::<usize, Vec<(&'a str, isize)>>::new();

    for (&curr_pos, curr_block) in blocks.iter().rev() {
        let calls_with_deltas_from_next = |next: &Next| -> Vec<(&'a str, isize)> {
            match next {
                // TODO remove expensive vector clone
                Next::Block(next_pos) => path_calls_with_deltas.get(next_pos).expect("Referenced block's func calls with deltas should have already been analyzed").clone(),
                Next::Terminate => vec![],
                Next::Trap => vec![],
            }
        };

        let terminator_calls_with_deltas = match &curr_block.terminator {
            Terminator::Jump(next) => calls_with_deltas_from_next(next),
            Terminator::If { on_true, on_false } => combine_sequential_calls_with_deltas(
                (vec![], Delta::Num(-1)),
                combine_branching_calls_with_deltas(
                    calls_with_deltas_from_next(on_true),
                    calls_with_deltas_from_next(on_false),
                ),
            ),
            Terminator::Skip { targets } => combine_sequential_calls_with_deltas(
                (vec![], Delta::Num(-1)),
                targets.iter().map(calls_with_deltas_from_next).fold(
                    calls_with_deltas_from_next(&Next::Trap),
                    combine_branching_calls_with_deltas,
                ),
            ),
        };

        let curr_path_calls_with_deltas = curr_block
            .code
            .iter()
            .map(|basic_block_instr| {
                (
                    basic_block_instr_to_calls_with_deltas(basic_block_instr),
                    basic_block_instr.delta(&known_deltas),
                )
            })
            .rev()
            .fold(terminator_calls_with_deltas, |r, l| {
                combine_sequential_calls_with_deltas(l, r)
            });

        path_calls_with_deltas.insert(curr_pos, curr_path_calls_with_deltas);
    }

    path_calls_with_deltas.get(&0).map_or(vec![], Clone::clone)
}

fn delta_and_reach_to_resolved_sig(d: &Delta, r: &Reach) -> Option<ResolvedSig> {
    match (d, r) {
        (Delta::Num(d), Reach::Num(r)) => Some(ResolvedSig {
            delta: Some(*d),
            reach: *r,
        }),
        (Delta::Never, Reach::Num(r)) => Some(ResolvedSig {
            delta: None,
            reach: *r,
        }),
        (Delta::NotWellBehaved, _) => None,
        (_, Reach::Unbounded) => None,
    }
}
