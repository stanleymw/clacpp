use std::collections::{BTreeMap, BTreeSet};

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use cranelift::prelude::Signature;

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

pub(crate) fn analyze<'names, 'instrs>(
    graph: &petgraph::Graph<Vec<&'names str>, ()>,
    funcs: &HashMap<&str, &'instrs [types::Instr]>,
) -> AnalysisResult<'names> {
    todo!()
}
