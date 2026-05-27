use std::collections::{BTreeMap, BTreeSet};

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use cranelift::prelude::Signature;

use crate::types::{self, BasicBlockInstr, CRANELIFT_VALUE, ControlFlowInstr, Instr};

use rayon::prelude::*;

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

        // --- Do infinite-reach detection ---
        // todo!();

        // --- Find reaches ---
        // todo!();
    }

    println!("--- Deltas Found ---");
    println!("{:#?}", all_deltas);

    todo!();

    // Combine Deltas and Reaches into ResolvedSigs
    let all_sigs: HashMap<&str, ResolvedSig> = funcs
        .iter()
        .flat_map(|(&func_name, _)| {
            delta_and_reach_to_resolved_sig(
                all_deltas
                    .get(func_name)
                    .expect("Function should have been analyzed for delta"),
                all_reaches
                    .get(func_name)
                    .expect("Function should have been analyzed for reach"),
            )
            .map_or(vec![], |sig| vec![(func_name, sig)])
        })
        .collect();

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
    Inconsistent,
}

fn combine_sequential_deltas(d1: Delta, d2: Delta) -> Delta {
    use Delta::*;
    match (d1, d2) {
        (Never, _) => Never,
        (_, Never) => Never,
        (Num(d1), Num(d2)) => Num(d1 + d2),
        _ => Inconsistent,
    }
}

fn combine_branching_deltas(d1: Delta, d2: Delta) -> Delta {
    use Delta::*;
    match (d1, d2) {
        (Never, d2) => d2,
        (d1, Never) => d1,
        (Num(d1), Num(d2)) if d1 == d2 => Num(d1),
        _ => Inconsistent,
    }
}

#[derive(PartialEq, Clone, Debug)]
pub(crate) enum Reach {
    Num(usize),
    Infinite,
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
        (Delta::Inconsistent, _) => None,
        (_, Reach::Infinite) => None,
    }
}

fn find_func_delta(blocks: &BTreeMap<usize, Block>, known: &HashMap<&str, Delta>) -> Delta {
    // A given block's associated path delta is the delta of starting with that block and going to the end of the function
    let mut path_deltas = BTreeMap::<usize, Delta>::new();

    // for loop must be backward (takes advantage of Clac control flow)
    for (&curr_pos, curr_block) in blocks.iter().rev() {
        // Add together body
        let curr_delta = curr_block
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
        let curr_delta = combine_sequential_deltas(
            curr_delta,
            match &curr_block.terminator {
                Terminator::Jump(next) => delta_from_next(next),
                Terminator::If { on_true, on_false } => {
                    combine_branching_deltas(delta_from_next(on_true), delta_from_next(on_false))
                }
                Terminator::Skip { targets } => targets
                    .iter()
                    .map(delta_from_next)
                    .fold(Delta::Never, combine_branching_deltas),
            },
        );

        path_deltas.insert(curr_pos, curr_delta);
    }
    // Default delta for empty function is 0
    path_deltas.get(&0).map_or(Delta::Num(0), Clone::clone)
}
