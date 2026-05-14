mod builtins;
mod jit;
pub mod types;

use ahash::{HashMap, HashMapExt};

use cranelift::prelude::isa::OwnedTargetIsa;
use cranelift_jit::JITModule;
use cranelift_module::ModuleError;
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};
use thiserror::Error;
use types::*;

use crate::jit::jit::{CompilerError, get_function};

fn parse(token: &str) -> Token {
    use Token::*;

    match token {
        "print" => Print,
        "quit" => Quit,

        "drop" => Drop,
        "swap" => Swap,
        "rot" => Rot,
        "pick" => Pick,

        "if" => If,
        "skip" => Skip,

        ":" => Colon,
        ";" => Semicolon,

        // "syscall" => Syscall,
        id => match id.parse() {
            Ok(num) => Literal(num),
            Err(_) => Identifier(id.to_string()),
        },
    }
}

impl ClacState {
    fn execute(
        stack: &mut Stack,
        jit: &Option<(JITModule, HashMap<String, cranelift_module::FuncId>)>,
        token: &Instr,
    ) -> Result<ExecRes, ExecError> {
        let mut xpop = || stack.pop().ok_or(ExecError::MissingArguments);

        match token {
            Instr::CFInstr(x) => match x {
                ControlFlowInstr::If => match xpop()? {
                    0 => Ok(ExecRes::Skip(3)),
                    _ => Ok(ExecRes::Executed),
                },
                ControlFlowInstr::Skip => Ok(ExecRes::Skip(
                    xpop()?.try_into().map_err(|_| ExecError::InvalidSkip)?,
                )),
            },
            Instr::BBInstr(x) => match x {
                BasicBlockInstr::Literal(n) => {
                    stack.push(*n);
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Quit => Err(ExecError::Quit),
                BasicBlockInstr::FunctionCall(state) => {
                    let Some((module, map)) = jit else {
                        panic!("No JIT")
                    };

                    let Some(f) = map.get(state) else {
                        return Err(ExecError::UnknownFunction(state.to_string()));
                    };

                    let asm = get_function(module, *f);

                    let new_rsp = unsafe { asm(stack.rsp) };
                    stack.rsp = new_rsp;

                    Ok(ExecRes::Executed)
                }

                BasicBlockInstr::Print => {
                    println!("{}", xpop()?);
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Drop => {
                    xpop()?;
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Swap => {
                    let b = xpop()?;
                    let a = xpop()?;

                    stack.push(b);
                    stack.push(a);

                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Rot => {
                    let z = xpop()?;
                    let y = xpop()?;
                    let x = xpop()?;

                    stack.push(y);
                    stack.push(z);
                    stack.push(x);
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Arith(it) => {
                    let b = xpop()?;
                    let a = xpop()?;
                    stack.push(match it {
                        ArithOp::Add => a + b,
                        ArithOp::Sub => a - b,
                        ArithOp::Mul => a * b,
                        ArithOp::Div => a / b,
                        ArithOp::Rem => a % b,
                        ArithOp::Lt => {
                            if a < b {
                                1
                            } else {
                                0
                            }
                        }
                        ArithOp::Pow => builtins::pow(a, b).ok_or(ExecError::InvalidExponent)?,
                    });
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Mem(memop) => {
                    match memop {
                        MemOp::Read8 => {
                            let addr = xpop()?;
                            let val = (unsafe { *(addr as *const u8) }) as Value;
                            stack.push(val);
                        }

                        MemOp::Write8 => {
                            let value: u8 = xpop()?
                                .try_into()
                                .expect("trying to write8 on a value that doesn't fit in a byte");

                            let addr = xpop()?;

                            let ptr = addr as *mut u8;
                            unsafe {
                                *ptr = value;
                            }
                        }

                        MemOp::ReadNative => {
                            let addr = xpop()?;
                            let val = (unsafe { *(addr as *const Value) }) as Value;
                            stack.push(val);
                        }

                        MemOp::WriteNative => {
                            let value: Value = xpop()?;
                            let addr = xpop()?;

                            let ptr = addr as *mut Value;
                            unsafe {
                                *ptr = value;
                            }
                        }

                        MemOp::WidthNative => {
                            stack.push(Value::BITS.into());
                        }
                    };
                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::Syscall => {
                    let v6 = xpop()?;
                    let v5 = xpop()?;
                    let v4 = xpop()?;
                    let v3 = xpop()?;
                    let v2 = xpop()?;
                    let v1 = xpop()?;
                    let rax = xpop()?;

                    stack.push(unsafe { builtins::syscall(rax, v1, v2, v3, v4, v5, v6) });

                    Ok(ExecRes::Executed)
                }

                BasicBlockInstr::ResolvedPick(n) => {
                    let val = stack.rsp.wrapping_sub(*n);

                    // TODO: undefined behavior for invalid picks?
                    stack.push(unsafe { *val });

                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::BadPick => {
                    let conv: usize = xpop()?.try_into().map_err(|_| ExecError::InvalidPick)?;

                    let true = conv > 0 else {
                        return Err(ExecError::InvalidPick);
                    };

                    let val = stack.rsp.wrapping_sub(conv);

                    // TODO: undefined behavior for invalid picks?
                    stack.push(unsafe { *val });

                    Ok(ExecRes::Executed)
                }

                &BasicBlockInstr::ResolvedDropRange { start, amt: amount } => {
                    let drop_start = stack.rsp.wrapping_sub(start);

                    let drop_end = drop_start.wrapping_add(amount);

                    debug_assert!(stack.rsp >= drop_end);

                    let keep_amount = start - amount;
                    debug_assert_eq!(
                        unsafe { stack.rsp.offset_from_unsigned(drop_end) },
                        keep_amount
                    );

                    unsafe { std::ptr::copy(drop_end, drop_start, keep_amount) };

                    stack.rsp = stack.rsp.wrapping_sub(amount);

                    Ok(ExecRes::Executed)
                }
                BasicBlockInstr::BadDropRange => {
                    let amount: usize = xpop()?
                        .try_into()
                        .map_err(|_| ExecError::InvalidDropRange)?;
                    let start: usize = xpop()?
                        .try_into()
                        .map_err(|_| ExecError::InvalidDropRange)?;

                    let true = amount <= start else {
                        return Err(ExecError::InvalidDropRange);
                    };

                    let drop_start = stack.rsp.wrapping_sub(start);

                    let drop_end = drop_start.wrapping_add(amount);

                    debug_assert!(stack.rsp >= drop_end);

                    let keep_amount = start - amount;
                    debug_assert_eq!(
                        unsafe { stack.rsp.offset_from_unsigned(drop_end) },
                        keep_amount
                    );

                    unsafe { std::ptr::copy(drop_end, drop_start, keep_amount) };

                    stack.rsp = stack.rsp.wrapping_sub(amount);

                    Ok(ExecRes::Executed)
                }
            },
        }
    }

    // we have to split execute_line and this version, due to lifetime problems. When you call clac functions, it will be executing in this context, where the FunctionMap CANNOT be modified, since you cannot define functions within a function.
    fn exec_function<'cs>(
        stack: &mut Stack,
        jit: &Option<(JITModule, HashMap<String, cranelift_module::FuncId>)>,
        mut callstack: CallStack<'cs>,
    ) -> Result<(), ExecError> {
        while let Some(line) = callstack.pop() {
            // println!("cs = {callstack:?}");
            let Some((token, xs)) = line.split_first() else {
                continue;
            };

            let mut optimize_push = |vals: &[Instr]| match vals {
                [] => {}
                [
                    Instr::BBInstr(BasicBlockInstr::Literal(n)),
                    Instr::CFInstr(ControlFlowInstr::Skip),
                    rest @ ..,
                ] if (*n >= 0 && ((*n as usize) == rest.len())) => {}
                _ => {
                    callstack.push(xs);
                }
            };

            match Self::execute(stack, jit, token)? {
                ExecRes::Executed => {
                    if !xs.is_empty() {
                        callstack.push(xs);
                    }
                }
                ExecRes::Skip(n) => match xs.split_at_checked(n) {
                    Some((_, remain)) => {
                        if !remain.is_empty() {
                            callstack.push(remain);
                        }
                    }
                    None => return Err(ExecError::InvalidSkip),
                },
                // ExecRes::RecursiveCall(newfunc) => {
                //     // TODO: tailcall optimization
                //     optimize_push(xs);

                //     callstack.push(newfunc);
                // }
            }
        }

        Ok(())
    }

    fn reset_module_and_recompile_all(&mut self) {
        // update function map
        for (name, f) in self.undefined_functions.drain(..) {
            self.funcmap.insert(name, f);
        }

        assert!(self.undefined_functions.is_empty());

        // create new compiler
        let new = Compiler::new().unwrap();
        let mut out = new.compile(&self.funcmap).unwrap();

        out.0.finalize_definitions().unwrap();

        // Reset the JIT
        let old = std::mem::replace(&mut self.jit, Some(out));
        if let Some((old_module, _)) = old {
            unsafe { old_module.free_memory() };
        }
    }

    /// Execute a slice of [`Token`]s representing a line of Clac++ code.
    pub fn execute_tokens(&mut self, mut line: &[Token]) -> Result<(), ExecError> {
        let mut cur_func: Option<(&String, Code)> = None;

        let mut stack = &mut self.stack;

        loop {
            (line, cur_func) = match (line, cur_func) {
                ([Token::Colon, Token::Identifier(name), rem @ ..], None) => {
                    (rem, Some((name, Vec::new())))
                }
                ([Token::Semicolon, rem @ ..], Some((name, f))) => {
                    self.undefined_functions.push((name.to_string(), f));

                    // first, resolve function names to indices in FuncMap

                    (rem, None)
                }
                ([Token::Colon | Token::Semicolon, ..], _) => {
                    return Err(ExecError::BadFunctionDefinition);
                }
                ([tok, rem @ ..], Some((nm, mut f))) => {
                    f.push(tok.clone().to_instruction());
                    (rem, Some((nm, f)))
                }
                ([tok, rem @ ..], None) => {
                    if let Token::Identifier(_) = tok
                        && !self.undefined_functions.is_empty()
                    {
                        self.reset_module_and_recompile_all();

                        if let Some((jit, map)) = &self.jit {
                            for (name, func) in map {
                                println!(
                                    "Function {name} | Wrapper @ {:?}",
                                    jit.get_finalized_function(*func),
                                );
                            }
                        } else {
                            println!("No JIT!")
                        }

                        stack = &mut self.stack;
                    }

                    match Self::execute(stack, &self.jit, &tok.clone().to_instruction())? {
                        ExecRes::Executed => (rem, None),
                        ExecRes::Skip(n) => match rem.split_at_checked(n) {
                            Some((_, rem2)) => (rem2, None),
                            None => return Err(ExecError::InvalidSkip),
                        },
                        // ExecRes::RecursiveCall(f) => {
                        //     Self::exec_function(stack, &self.jit, vec![f])?;
                        //     (rem, None)
                        // }
                    }
                }
                ([], Some(_)) => return Err(ExecError::BadFunctionDefinition),
                ([], None) => return Ok(()),
            };
        }
    }

    /// Execute a line of Clac++ code in a string.
    pub fn execute_str(&mut self, line: &str) -> Result<(), ExecError> {
        let parsed: Vec<Token> = line.split_whitespace().map(parse).collect();

        self.execute_tokens(&parsed)
    }
}

#[derive(Debug, Error)]
pub enum AOTCompileError {
    #[error("Bad Function Definition")]
    BadFunctionDefinition,

    #[error("Top level is not allowed in Ahead of time compilation.")]
    TopLevelDisallowed,

    #[error("Cranelift module error: {0}")]
    CraneliftModuleError(#[from] ModuleError),

    #[error("Compile error: {0}")]
    CompileError(#[from] CompilerError),
}

fn extract_functions(mut line: &[Token]) -> Result<HashMap<&str, Code>, AOTCompileError> {
    let mut cur_func: Option<(&str, Code)> = None;
    let mut res: HashMap<&str, Code> = HashMap::new();

    // we need to ensure that it is all functions: NO TOP LEVEL
    loop {
        (line, cur_func) = match (line, cur_func) {
            ([Token::Colon, Token::Identifier(name), rem @ ..], None) => {
                (rem, Some((name.as_str(), Vec::new())))
            }
            ([Token::Semicolon, rem @ ..], Some((name, f))) => {
                res.insert(name, f);

                // first, resolve function names to indices in FuncMap

                (rem, None)
            }
            ([Token::Colon | Token::Semicolon, ..], _) => {
                return Err(AOTCompileError::BadFunctionDefinition);
            }
            ([tok, rem @ ..], Some((nm, mut f))) => {
                f.push(tok.clone().to_instruction());
                (rem, Some((nm, f)))
            }
            ([_, ..], None) => return Err(AOTCompileError::TopLevelDisallowed),
            ([], Some(_)) => return Err(AOTCompileError::BadFunctionDefinition),
            ([], None) => return Ok(res),
        };
    }
}

pub fn compile_tokens(
    line: &[Token],
    isa: OwnedTargetIsa,
    object_name: &str,
) -> Result<ObjectProduct, AOTCompileError> {
    let module = ObjectBuilder::new(isa, object_name, cranelift_module::default_libcall_names())?;
    let mut module = ObjectModule::new(module);

    let declared = declare_imports(&mut module)?;

    let compiler = Compiler {
        module,
        imports: declared,
    };

    let functions: FuncMap = extract_functions(line)?
        .into_iter()
        .map(|(name, code)| (name.to_string(), code))
        .collect();

    let res = compiler.compile(&functions)?;
    Ok(res.0.finish())
}

pub fn compile_str(
    line: &str,
    isa: OwnedTargetIsa,
    object_name: &str,
) -> Result<ObjectProduct, AOTCompileError> {
    let parsed: Vec<Token> = line.split_whitespace().map(parse).collect();

    compile_tokens(&parsed, isa, object_name)
}
