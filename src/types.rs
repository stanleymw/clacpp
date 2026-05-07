use core::{fmt, slice};
use std::fmt::Debug;
use std::io;

use ahash::HashMap;
use cranelift::{
    codegen::Context,
    prelude::{AbiParam, FunctionBuilderContext, Signature, types::I64},
};
use cranelift_jit::{ArenaMemoryProvider, JITBuilder, JITModule};
use cranelift_module::{FuncId, Module};
use thiserror::Error;

use crate::builtins;

use crate::jit::jit_builtins;

pub type Value = i64;
// TODO: submit PR TO MAKE Type::int CONST
// pub const CRANELIFT_VALUE: cranelift::prelude::Type = Type::int(Value::BITS).unwrap();
pub const CRANELIFT_VALUE: cranelift::prelude::Type = I64;

pub(crate) type ValueStack = Vec<Value>;

type FunctionIndex = usize;

// pub(crate) enum FuncRef {
//     Resolved(FunctionIndex),
//     Unresolved(String),
// }
#[derive(Debug, Clone)]
pub(crate) struct FuncRef(pub(crate) String);

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
pub(crate) enum MemOp {
    Read8,
    ReadNative,
    Write8,
    WriteNative,

    WidthNative,
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
    Syscall,

    // stack manipulation
    Drop,
    Swap,
    Rot,
    DropRange,

    Arith(ArithOp),
    Mem(MemOp),

    // Math Instructions
    If,
    Pick,
    Skip,
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
            Token::Literal(n) => Instr::Literal(n),
            Token::Identifier(name) if let Some(inst) = builtins::FUNCTIONS.get(name.as_str()) => {
                inst.clone()
            }
            Token::Identifier(name) => Instr::FunctionCall(FuncRef(name)),
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

pub(crate) type JITFunction = unsafe extern "C" fn(*mut Value) -> *mut Value;

#[derive(Debug, Clone)]
pub(crate) struct Function {
    pub(crate) code: Code,
    pub(crate) id: FuncId,
    pub(crate) wrapper_id: FuncId,
}

pub(crate) type CallStack<'a> = Vec<&'a [Instr]>;

#[derive(Debug, Default)]
pub(crate) struct FuncMap(pub(crate) HashMap<String, Function>);

impl FuncMap {
    pub(crate) fn lookup(&self, FuncRef(target): &FuncRef) -> Option<&Function> {
        self.0.get(target)
    }
}

// TODO: make a macro to do this
pub(crate) struct Imports {
    pub(crate) printfunc: FuncId,
    pub(crate) quitfunc: FuncId,
    pub(crate) powfunc: FuncId,
    pub(crate) syscallfunc: FuncId,
    pub(crate) errorfunc: FuncId,
}

pub(crate) struct Compiler<T> {
    pub(crate) module: T,
    pub(crate) fbctx: FunctionBuilderContext,
    pub(crate) ctx: Context,

    pub(crate) imports: Imports,
}

/// The primary struct representing the state of the Clac++ machine.
pub struct ClacState {
    // JIT Stuff
    pub(crate) jit: Compiler<JITModule>, // TODO: make JIT optional

    pub(crate) undefined_functions: Vec<(String, Code)>,
    // Clac Stuff
    pub(crate) stack: Stack,
    pub(crate) funcmap: FuncMap,
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

fn declare_imports(module: &mut impl Module) -> Result<Imports, cranelift_module::ModuleError> {
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

    let errorfunc = module.declare_function(
        "__rerror__",
        cranelift_module::Linkage::Import,
        &Signature {
            params: vec![valparam],
            returns: vec![],
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
        errorfunc,
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
        builder.symbol("__rerr__", jit_builtins::error as *const u8);
        builder.symbol("__rpow__", jit_builtins::pow as *const u8);
        builder.symbol("__syscall__", builtins::syscall as *const u8);

        let mut module = cranelift_jit::JITModule::new(builder);
        let ctx = module.make_context();

        let imports = declare_imports(&mut module)?;

        Ok(Compiler {
            module,
            fbctx: FunctionBuilderContext::new(),
            ctx,
            imports,
        })
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
            jit: Compiler::new()?,
            stack: Stack::new(capacity)?,
            undefined_functions: Vec::new(),
            funcmap: FuncMap::default(),
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
    #[error("Invalid DropRange")]
    InvalidDropRange,

    #[error("Bad function definition")]
    BadFunctionDefinition,
    #[error("Invalid exponent, must have non-negative exponent")]
    InvalidExponent,
    #[error("Quit")]
    Quit,
}
