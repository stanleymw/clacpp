use std::collections::HashMap;

pub type Value = i64;
pub type ClacStack = Vec<Value>;

#[derive(Debug, Clone)]
pub enum Token {
    // data
    Literal(Value),
    Function(String),

    // side effects
    Quit,
    Print,

    // syscall
    // Ptr,
    // Syscall,

    // stack manipulation
    Drop,
    Swap,
    Rot,

    If,
    Pick,
    Skip,

    // function stuff
    Colon,
    Semicolon,
}

pub type Code = Vec<Token>;

#[derive(Debug)]
pub enum Function {
    Clac(Code),

    Native(fn(&mut ClacStack)),

    ClacOp(fn(Value, Value) -> Value),
}

pub type FuncMap = HashMap<String, Function>;
pub type CallStack<'a> = Vec<&'a [Token]>;

#[derive(Debug)]
pub struct ClacState {
    pub stack: ClacStack,
    pub funcmap: FuncMap,
}

pub enum ExecRes<'a> {
    Executed,
    Skip(usize),
    RecursiveCall(&'a [Token]),
    Quit,
}

pub enum LineRes {
    Executed,
    Quit,
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum ExecError {
    UnknownFunction(String),
    MissingArguments,
    InvalidSkip,
    InvalidPick,
    BadFunctionDefinition,
}
