use std::collections::HashMap;

pub type Value = i64;
pub type ClacStack = Vec<Value>;

// pub enum ClacBinOp {
//     ArithOp(fn(ClacValue, ClacValue) -> ClacValue),
// }

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

type Code = Vec<Token>;

pub enum Function {
    Clac(Code),
    Native2(fn(Value, Value) -> Value),
}

pub type FuncMap = HashMap<String, Function>;

pub struct ClacState {
    pub stack: ClacStack,
    pub functions: FuncMap,
}
