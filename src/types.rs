use core::{fmt, slice};
use std::fmt::Debug;
use std::io;

use ahash::{HashMap, HashMapExt};
use cranelift::prelude::{AbiParam, Signature, types::I64};
use cranelift_jit::{ArenaMemoryProvider, JITBuilder, JITModule};
use cranelift_module::{FuncId, Module};
use thiserror::Error;

use crate::builtins;

use crate::jit::analysis::ResolvedSig;
use crate::jit::jit_builtins;

pub type Value = i64;
// TODO: submit PR TO MAKE Type::int CONST
// pub const CRANELIFT_VALUE: cranelift::prelude::Type = Type::int(Value::BITS).unwrap();
pub const CRANELIFT_VALUE: cranelift::prelude::Type = I64;

// pub(crate) enum FuncRef {
//     Resolved(FunctionIndex),
//     Unresolved(String),
// }
// #[derive(Debug, Clone)]
// pub(crate) struct FuncRef(pub(crate) String);

#[derive(Debug, Clone)]
pub(crate) enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Pow,
}

#[derive(Debug, Clone)]
pub(crate) enum BasicBlockInstr {
    // data
    Literal(Value),       // delta = 1, reach = 0
    FunctionCall(String), // delta = -argc + return_count, reach = argc

    // side effects
    Quit,    // delta = !, reach = 0
    Print,   // delta = -1, reach = 1
    Syscall, // delta = -6, reach = 7

    // stack manipulation
    Drop, // delta = -1, reach = 1
    Swap, // delta = 0, reach = 2
    Rot,  // delta = 0, reach = 3

    // PRECONDITION: start >= amt
    ResolvedDropRange { start: usize, amt: usize }, // <start> <amt> drop_range => delta = -amt , reach = start
    BadDropRange,

    // PRECONDITION: amt >= 1
    ResolvedPick(usize), // <amt> pick => delta = 1, reach = amt
    BadPick,             // delta = 0, reach = indeterminate

    // Math/Memory Instructions
    Arith(ArithOp), // delta = -1, reach = 2
    Mem(MemOp),     // see `MemOp`
}

pub enum ResolveErr<'a> {
    FunctionUnresolved(&'a str),
    NotDeterminable,
    Anything,
}

impl BasicBlockInstr {
    pub fn delta(&self, funcs: &HashMap<&str, ResolvedSig>) -> Result<i64, ResolveErr<'_>> {
        use ResolveErr::*;

        match self {
            BasicBlockInstr::Literal(_) => Ok(1),
            BasicBlockInstr::FunctionCall(name) => {
                let sig = funcs.get(name.as_str()).ok_or(FunctionUnresolved(name))?;

                sig.delta.ok_or_else(|| Anything)
            }
            BasicBlockInstr::Quit => Err(Anything),
            BasicBlockInstr::Print => Ok(-1),
            BasicBlockInstr::Syscall => Ok(-6),
            BasicBlockInstr::Drop => Ok(-1),
            BasicBlockInstr::Swap => Ok(0),
            BasicBlockInstr::Rot => Ok(0),
            BasicBlockInstr::ResolvedDropRange { start: _, amt } => Ok(-(*amt as i64)),
            BasicBlockInstr::BadDropRange => Err(NotDeterminable),
            BasicBlockInstr::ResolvedPick(_) => Ok(1),
            BasicBlockInstr::BadPick => Ok(0),
            BasicBlockInstr::Arith(_) => Ok(-1),
            BasicBlockInstr::Mem(mem_op) => Ok(mem_op.delta()),
        }
    }

    pub fn reach(&self, funcs: &HashMap<&str, ResolvedSig>) -> Result<usize, ResolveErr<'_>> {
        use ResolveErr::*;

        match self {
            BasicBlockInstr::Literal(_) => Ok(0),
            BasicBlockInstr::FunctionCall(name) => {
                let sig = funcs.get(name.as_str()).ok_or(FunctionUnresolved(name))?;

                Ok(sig.reach)
            }
            BasicBlockInstr::Quit => Ok(0),
            BasicBlockInstr::Print => Ok(1),
            BasicBlockInstr::Syscall => Ok(7),
            BasicBlockInstr::Drop => Ok(1),
            BasicBlockInstr::Swap => Ok(2),
            BasicBlockInstr::Rot => Ok(3),
            BasicBlockInstr::ResolvedDropRange { start, amt: _ } => Ok(*start),
            BasicBlockInstr::BadDropRange => Err(NotDeterminable),
            BasicBlockInstr::ResolvedPick(n) => Ok(*n),
            BasicBlockInstr::BadPick => Err(NotDeterminable),
            BasicBlockInstr::Arith(_) => Ok(2),
            BasicBlockInstr::Mem(mem_op) => Ok(mem_op.reach()),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum MemOp {
    Read8,       // delta = 0, reach = 1
    ReadNative,  // delta = 0, reach = 1
    Write8,      // delta = -2, reach = 2
    WriteNative, // delta = -2, reach = 2

    WidthNative, // delta = 1, reach = 0
}

impl MemOp {
    fn delta(&self) -> i64 {
        match self {
            MemOp::Read8 => 0,
            MemOp::ReadNative => 0,

            MemOp::Write8 => -2,
            MemOp::WriteNative => -2,

            MemOp::WidthNative => 1,
        }
    }

    fn reach(&self) -> usize {
        match self {
            MemOp::Read8 => 1,
            MemOp::ReadNative => 1,

            MemOp::Write8 => 2,
            MemOp::WriteNative => 2,

            MemOp::WidthNative => 0,
        }
    }
}

// Theorem:
// total delta >= -(peak reach)

#[derive(Debug, Clone)]
pub(crate) enum ControlFlowInstr {
    If,
    Skip,
}

impl ControlFlowInstr {
    pub fn delta(&self) -> i64 {
        match self {
            ControlFlowInstr::If => -1,
            ControlFlowInstr::Skip => -1,
        }
    }

    pub fn reach(&self) -> usize {
        match self {
            ControlFlowInstr::If => 1,
            ControlFlowInstr::Skip => 1,
        }
    }
}

#[derive(Debug, Clone)]
// Internal clac instruction
pub(crate) enum Instr {
    BBInstr(BasicBlockInstr),
    // Control Flow
    CFInstr(ControlFlowInstr),
}

impl Instr {
    pub fn delta(&self, funcs: &HashMap<&str, ResolvedSig>) -> Result<i64, ResolveErr<'_>> {
        match self {
            Instr::BBInstr(basic_block_instr) => basic_block_instr.delta(funcs),
            Instr::CFInstr(control_flow_instr) => Ok(control_flow_instr.delta()),
        }
    }

    pub fn reach(&self, funcs: &HashMap<&str, ResolvedSig>) -> Result<usize, ResolveErr<'_>> {
        match self {
            Instr::BBInstr(basic_block_instr) => basic_block_instr.reach(funcs),
            Instr::CFInstr(control_flow_instr) => Ok(control_flow_instr.reach()),
        }
    }
}

impl From<BasicBlockInstr> for Instr {
    fn from(value: BasicBlockInstr) -> Self {
        Self::BBInstr(value)
    }
}

impl From<ControlFlowInstr> for Instr {
    fn from(value: ControlFlowInstr) -> Self {
        Self::CFInstr(value)
    }
}

impl TryFrom<Instr> for BasicBlockInstr {
    type Error = Instr;

    fn try_from(value: Instr) -> Result<Self, Instr> {
        match value {
            Instr::BBInstr(basic_block_instr) => Ok(basic_block_instr),
            x @ Instr::CFInstr(_) => Err(x),
        }
    }
}

impl TryFrom<Instr> for ControlFlowInstr {
    type Error = Instr;

    fn try_from(value: Instr) -> Result<Self, Instr> {
        match value {
            Instr::CFInstr(cfinstr) => Ok(cfinstr),
            x @ Instr::BBInstr(_) => Err(x),
        }
    }
}

#[derive(Debug, Clone)]
/// Represents a parsed string token.
pub enum Token {
    // data
    Literal(Value),
    Identifier(String),

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
    pub(crate) fn to_instruction(self) -> Instr {
        match self {
            Token::Literal(n) => BasicBlockInstr::Literal(n).into(),
            Token::Identifier(name) if let Some(inst) = builtins::FUNCTIONS.get(name.as_str()) => {
                inst.clone()
            }
            Token::Identifier(name) => BasicBlockInstr::FunctionCall(name).into(),
            Token::Quit => BasicBlockInstr::Quit.into(),
            Token::Print => BasicBlockInstr::Print.into(),
            Token::Drop => BasicBlockInstr::Drop.into(),
            Token::Swap => BasicBlockInstr::Swap.into(),
            Token::Rot => BasicBlockInstr::Rot.into(),
            Token::Pick => BasicBlockInstr::BadPick.into(),
            Token::If => ControlFlowInstr::If.into(),
            Token::Skip => ControlFlowInstr::Skip.into(),
            _ => unreachable!("Tried to convert function syntax into an instruction"),
        }
    }
}

pub(crate) type Code = Vec<Instr>;

// #[derive(Debug)]
// pub(crate) struct ClacFn {
//     code: Code,
// }

pub(crate) type JITFunction = unsafe extern "C" fn(*mut Value) -> *mut Value;

pub(crate) type CallStack<'a> = Vec<&'a [Instr]>;

// TODO: make a macro to do this
pub(crate) struct Imports {
    pub(crate) printfunc: FuncId,
    pub(crate) quitfunc: FuncId,
    pub(crate) powfunc: FuncId,
    pub(crate) syscallfunc: FuncId,
}

pub(crate) struct Compiler<T> {
    pub(crate) module: T,

    pub(crate) imports: Imports,
}

pub(crate) type FuncMap = HashMap<String, Code>;

/// The primary struct representing the state of the Clac++ machine.
pub struct ClacState {
    // JIT Stuff
    pub(crate) jit: Option<(JITModule, HashMap<String, FuncId>)>, // TODO: make JIT optional

    pub(crate) undefined_functions: Vec<(String, Code)>,
    // Clac Stuff
    pub(crate) stack: Stack,
    pub(crate) funcmap: FuncMap, // Map of defined functions
}

pub(crate) struct Stack {
    data: memmap2::MmapMut,
    pub(crate) rsp: *mut Value,
    // TODO: check if compiler optimizes out get head pointer
}

impl Debug for Stack {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let head = self.data.as_ptr() as *const Value;
        let len = unsafe {
            self.rsp
                .offset_from_unsigned(self.data.as_ptr() as *const Value)
        };

        <[Value] as Debug>::fmt(unsafe { slice::from_raw_parts(head, len) }, fmt)
    }
}

impl Stack {
    fn new(capacity: usize) -> io::Result<Self> {
        let mut alloced = memmap2::MmapMut::map_anon(capacity)?;
        Ok(Self {
            rsp: alloced.as_mut_ptr() as *mut Value,
            data: alloced,
        })
    }

    pub(crate) fn push(&mut self, val: Value) {
        unsafe {
            *self.rsp = val;
        }
        self.rsp = self.rsp.wrapping_offset(1);
    }

    pub(crate) fn pop(&mut self) -> Option<Value> {
        if self.rsp == self.data.as_mut_ptr() as *mut Value {
            None
        } else {
            self.rsp = self.rsp.wrapping_offset(-1);
            Some(unsafe { *self.rsp })
        }
    }
}

#[derive(Debug, Error)]
pub enum InitError {
    #[error("Module error: {0}")]
    ModuleError(#[from] cranelift_module::ModuleError),
    #[error("IO Error: {0}")]
    IoError(#[from] io::Error),
}

pub(crate) fn declare_imports(
    module: &mut impl Module,
) -> Result<Imports, cranelift_module::ModuleError> {
    let valparam = AbiParam::new(CRANELIFT_VALUE);

    // TODO: make better
    let printfunc = module.declare_function(
        "__rprint__",
        cranelift_module::Linkage::Import,
        &Signature {
            params: vec![valparam],
            returns: vec![],
            call_conv: module.isa().default_call_conv(),
        },
    )?;

    let syscallfunc = module.declare_function(
        "__syscall__",
        cranelift_module::Linkage::Import,
        &Signature {
            params: vec![
                valparam, valparam, valparam, valparam, valparam, valparam, valparam,
            ],
            returns: vec![valparam],
            call_conv: module.isa().default_call_conv(),
        },
    )?;

    let quitfunc = module.declare_function(
        "__rquit__",
        cranelift_module::Linkage::Import,
        &Signature {
            params: vec![],
            returns: vec![],
            call_conv: module.isa().default_call_conv(),
        },
    )?;

    let powfunc = module.declare_function(
        "__rpow__",
        cranelift_module::Linkage::Import,
        &Signature {
            params: vec![valparam, valparam],
            returns: vec![valparam],
            call_conv: module.isa().default_call_conv(),
        },
    )?;

    Ok(Imports {
        printfunc,
        quitfunc,
        powfunc,
        syscallfunc,
    })
}

impl Compiler<JITModule> {
    pub(crate) fn new() -> Result<Self, InitError> {
        let mut builder = JITBuilder::with_flags(
            &[
                ("opt_level", "speed"),
                ("enable_alias_analysis", "true"),
                // TODO: remove this if we can do tailcalls without it
                ("preserve_frame_pointers", "true"),
            ],
            cranelift_module::default_libcall_names(),
        )?;

        // TODO: maybe replace with the old system allocator (?)
        builder.memory_provider(Box::new(
            ArenaMemoryProvider::new_with_size(1_000_000_000).unwrap(),
        ));

        builder.symbol("__rprint__", jit_builtins::print_value as *const u8);
        builder.symbol("__rquit__", jit_builtins::quit as *const u8);
        builder.symbol("__rpow__", jit_builtins::pow as *const u8);
        builder.symbol("__syscall__", builtins::syscall as *const u8);

        let mut module = cranelift_jit::JITModule::new(builder);

        let imports = declare_imports(&mut module)?;

        Ok(Compiler { module, imports })
    }
}

#[derive(Debug, Error)]
pub enum ReplError {
    #[error("Execution Error: {0}")]
    ExecError(#[from] ExecError),

    #[error("Readline Error: {0}")]
    LineError(#[from] rustyline::error::ReadlineError),

    #[error("Init error: {0}")]
    InitError(#[from] InitError),
}

impl ClacState {
    pub fn new(capacity: usize) -> Result<Self, InitError> {
        Ok(ClacState {
            jit: None,
            stack: Stack::new(capacity)?,
            undefined_functions: Vec::new(),
            funcmap: HashMap::new(),
        })
    }

    /// Launch an interactive REPL on the provided ClacState.
    pub fn repl(&mut self, hide_stack: bool) -> Result<(), ReplError> {
        println!("clac++ {} by stanleymw", env!("CARGO_PKG_VERSION"),);

        let mut editor = rustyline::DefaultEditor::new()?;

        loop {
            let read = match editor.readline("clac++> ") {
                Err(rustyline::error::ReadlineError::Eof)
                | Err(rustyline::error::ReadlineError::Interrupted) => {
                    return Ok(());
                }
                Err(e) => return Err(e.into()),
                Ok(res) => {
                    editor.add_history_entry(&res)?;
                    res
                }
            };

            if cfg!(feature = "debug") && read == "int3" {
                unsafe { std::arch::asm!("int3") };
                continue;
            }

            match self.execute_str(&read) {
                Err(ExecError::Quit) => return Ok(()),
                Err(x) => return Err(x.into()),
                Ok(()) => {}
            };

            if !hide_stack {
                println!("{:?}", self.stack)
            }
        }
    }
}

pub(crate) enum ExecRes {
    Executed,
    Skip(usize),
    // TODO: add this back for Non-JIT mode
    // RecursiveCall(&'a [Instr]),
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
    #[error("Invalid DropRange")]
    InvalidDropRange,

    #[error("Bad function definition")]
    BadFunctionDefinition,
    #[error("Invalid exponent, must have non-negative exponent")]
    InvalidExponent,
    #[error("Quit")]
    Quit,
}
