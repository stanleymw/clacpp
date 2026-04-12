use thiserror::Error;

use crate::builtins;

pub type Value = i64;
pub(crate) type ValueStack = Vec<Value>;

type FunctionIndex = usize;

#[derive(Debug, Clone)]
pub(crate) enum FuncRef {
    Resolved(FunctionIndex),
    Unresolved(String),
}

#[derive(Debug, Clone)]
// Internal clac instruction
pub(crate) enum Instr {
    // data
    Literal(Value),
    FunctionCall(FuncRef),

    // side effects
    Quit,
    Print,

    // stack manipulation
    Drop,
    Swap,
    Rot,

    // Math Instructions
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    If,
    Pick,
    Skip,
}

#[derive(Debug, Clone)]
/// Represents a parsed string token.
pub enum Token {
    // data
    Literal(Value),
    FunctionCall(String),

    // side effects
    Quit,
    Print,

    // stack manipulation
    Drop,
    Swap,
    Rot,

    If,
    Pick,
    Skip,

    // function definition syntax
    Colon,
    Semicolon,
}

impl Token {
    // TODO: maybe it's unnecessary to own the instructions?
    pub(crate) fn token_to_instruction(self, functions: &FuncMap) -> Instr {
        match self {
            Token::Literal(n) => Instr::Literal(n),
            Token::FunctionCall(name) => match functions.map.get(&name) {
                Some(idx) => match &functions.functions[*idx] {
                    Function::ClacInstr(inst) => inst.clone(),
                    _ => Instr::FunctionCall(FuncRef::Resolved(*idx)),
                },
                None => Instr::FunctionCall(FuncRef::Unresolved(name)),
            },
            Token::Quit => Instr::Quit,
            Token::Print => Instr::Print,
            Token::Drop => Instr::Drop,
            Token::Swap => Instr::Swap,
            Token::Rot => Instr::Rot,
            Token::If => Instr::If,
            Token::Skip => Instr::Skip,
            Token::Pick => Instr::Pick,
            _ => unreachable!("Tried to convert function syntax into an instruction"),
        }
    }
}

pub(crate) type Code = Vec<Instr>;

// #[derive(Debug)]
// pub(crate) struct ClacFn {
//     code: Code,
// }

#[derive(Debug)]
pub(crate) enum Function {
    Clac(Code),

    Native(fn(&mut ValueStack)),

    ClacInstr(Instr),

    ClacOp(fn(Value, Value) -> Value),
}

pub(crate) type CallStack<'a> = Vec<&'a [Instr]>;

#[derive(Debug)]
pub(crate) struct FuncMap {
    pub(crate) map: ahash::AHashMap<String, FunctionIndex>,
    pub(crate) functions: Vec<Function>,
}

fn name_func_pair_to_funcmap<const N: usize>(xs: [(&str, Function); N]) -> FuncMap {
    FuncMap {
        map: ahash::AHashMap::from_iter(
            xs.iter()
                .enumerate()
                .map(|(i, (name, _))| (name.to_string(), i)),
        ),
        functions: Vec::from_iter(xs.into_iter().map(|(_, func)| func)),
    }
}

#[derive(Debug)]
/// The primary struct representing the state of the Clac++ machine.
pub struct ClacState {
    pub(crate) stack: ValueStack,
    pub(crate) funcmap: FuncMap,
}

impl Default for ClacState {
    fn default() -> Self {
        ClacState {
            stack: Vec::new(),
            funcmap: name_func_pair_to_funcmap(builtins::FUNCTIONS),
        }
    }
}

impl ClacState {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            stack: Vec::with_capacity(capacity),
            funcmap: name_func_pair_to_funcmap(builtins::FUNCTIONS),
        }
    }
}

pub(crate) enum ExecRes<'a> {
    Executed,
    Skip(usize),
    RecursiveCall(&'a [Instr]),
}

#[derive(Debug, Error)]
pub enum ExecError {
    #[error("Unknown function {0}")]
    UnknownFunction(String),
    #[error("Missing arguments. Not enough elements on stack")]
    MissingArguments,
    #[error("Invalid Skip")]
    InvalidSkip,
    #[error("Invalid Pick")]
    InvalidPick,
    #[error("Bad function definition")]
    BadFunctionDefinition,
    #[error("Quit")]
    Quit,
}
