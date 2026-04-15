use core::{fmt, slice};
use std::fmt::Debug;
use std::{io, process::exit};

use cranelift::{
    codegen::Context,
    prelude::{AbiParam, FunctionBuilderContext, Signature, types::I64},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Module};
use thiserror::Error;

use crate::builtins;

pub type Value = i64;
pub const CRANELIFT_VALUE: cranelift::prelude::Type = I64;

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

pub(crate) struct Imports {
    pub(crate) printfunc: FuncId,
    pub(crate) quitfunc: FuncId,
}

pub(crate) struct JITState {
    pub(crate) module: JITModule,
    pub(crate) ctx: Context,
    pub(crate) fbctx: FunctionBuilderContext,

    pub(crate) imports: Imports,
}

/// The primary struct representing the state of the Clac++ machine.
pub struct ClacState {
    // JIT Stuff
    pub(crate) jit: JITState,

    // Clac Stuff
    pub(crate) stack: Stack,
    pub(crate) funcmap: FuncMap,
}

// extern "C" fn rpush(stack: *mut ValueStack, val: i64) {
//     match unsafe { stack.as_mut() } {
//         None => exit(67),
//         Some(v) => {
//             v.push(val);
//         }
//     }
// }

// extern "C" fn rpop(stack: *mut ValueStack) -> Value {
//     match unsafe { stack.as_mut() } {
//         None => exit(68),
//         Some(v) => match v.pop() {
//             None => exit(69),
//             Some(n) => n,
//         },
//     }
// }

extern "C" fn quit() {
    exit(0);
}

extern "C" fn print_value(val: Value) {
    println!("{}", val)
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

impl ClacState {
    pub fn new(capacity: usize) -> Result<Self, InitError> {
        let mut builder = JITBuilder::with_flags(
            &[("opt_level", "speed")],
            cranelift_module::default_libcall_names(),
        )?;

        builder.symbol("__rprint__", print_value as *const u8);
        builder.symbol("__rquit__", quit as *const u8);

        let mut module = cranelift_jit::JITModule::new(builder);

        let printfunc = module.declare_function(
            "__rprint__",
            cranelift_module::Linkage::Import,
            &Signature {
                params: vec![AbiParam::new(CRANELIFT_VALUE)],
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

        let ctx = module.make_context();

        Ok(ClacState {
            jit: JITState {
                module,
                ctx,
                fbctx: FunctionBuilderContext::new(),
                imports: Imports {
                    printfunc: printfunc,
                    quitfunc: quitfunc,
                },
            },
            stack: Stack::new(capacity)?,
            funcmap: name_func_pair_to_funcmap(builtins::FUNCTIONS),
        })
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
