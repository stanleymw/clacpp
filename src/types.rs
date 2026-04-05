pub type Value = i64;
pub type ClacStack = Vec<Value>;

type FunctionIndex = usize;

#[derive(Debug, Clone)]
pub enum FunctionRef {
    Resolved(FunctionIndex),
    Unresolved(String),
}

#[derive(Debug, Clone)]
pub enum Token {
    // data
    Literal(Value),
    FunctionCall(FunctionRef),

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

// pub type FuncMap = ahash::AHashMap<String, FunctionIndex>;
pub type CallStack<'a> = Vec<&'a [Token]>;

#[derive(Debug)]
pub struct FuncMap {
    pub map: ahash::AHashMap<String, FunctionIndex>,
    pub functions: Vec<Function>,
}

#[derive(Debug)]
/// The primary struct representing the state of the Clac++ machine.
pub struct ClacState {
    pub stack: ClacStack,
    pub funcmap: FuncMap,
}

pub enum ExecRes<'a> {
    Executed,
    Skip(usize),
    RecursiveCall(&'a [Token]),
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum ExecError {
    UnknownFunction(String),
    MissingArguments,
    InvalidSkip,
    InvalidPick,
    BadFunctionDefinition,
    Quit,
}
