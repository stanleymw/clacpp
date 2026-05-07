mod builtins;
mod jit;
pub mod types;

use ahash::{HashMap, HashMapExt};

use cranelift::prelude::isa::OwnedTargetIsa;
use cranelift_jit::JITModule;
use cranelift_module::{Module, ModuleError};
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};
use thiserror::Error;
use types::*;

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
    fn execute<'cs>(
        functions: &'cs FuncMap,
        stack: &mut Stack,
        jit: &Compiler<JITModule>,
        token: &Instr,
    ) -> Result<ExecRes<'cs>, ExecError> {
        let mut xpop = || stack.pop().ok_or(ExecError::MissingArguments);

        match token {
            Instr::Literal(n) => {
                stack.push(*n);
                Ok(ExecRes::Executed)
            }
            Instr::Quit => Err(ExecError::Quit),
            Instr::FunctionCall(state) => {
                let Some(f) = functions.lookup(state) else {
                    return Err(ExecError::UnknownFunction(state.0.to_string()));
                };

                let asm = jit.get_function(f.id);

                let new_rsp = unsafe { asm(stack.rsp) };
                stack.rsp = new_rsp;

                Ok(ExecRes::Executed)
            }

            Instr::Print => {
                println!("{}", xpop()?);
                Ok(ExecRes::Executed)
            }
            Instr::Drop => {
                xpop()?;
                Ok(ExecRes::Executed)
            }
            Instr::Swap => {
                let b = xpop()?;
                let a = xpop()?;

                stack.push(b);
                stack.push(a);

                Ok(ExecRes::Executed)
            }
            Instr::Rot => {
                let z = xpop()?;
                let y = xpop()?;
                let x = xpop()?;

                stack.push(y);
                stack.push(z);
                stack.push(x);
                Ok(ExecRes::Executed)
            }
            Instr::If => match xpop()? {
                0 => Ok(ExecRes::Skip(3)),
                _ => Ok(ExecRes::Executed),
            },
            Instr::Skip => Ok(ExecRes::Skip(
                xpop()?.try_into().map_err(|_| ExecError::InvalidSkip)?,
            )),
            Instr::Arith(it) => {
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
            Instr::Mem(memop) => {
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
            Instr::Syscall => {
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
            Instr::Pick => {
                let conv: usize = xpop()?.try_into().map_err(|_| ExecError::InvalidPick)?;
                let val = stack.rsp.wrapping_sub(conv);

                // TODO: undefined behavior for invalid picks?
                stack.push(unsafe { *val });

                Ok(ExecRes::Executed)
            }
            Instr::DropRange => {
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
        }
    }

    // we have to split execute_line and this version, due to lifetime problems. When you call clac functions, it will be executing in this context, where the FunctionMap CANNOT be modified, since you cannot define functions within a function.
    fn exec_function<'cs>(
        funcs: &'cs FuncMap,
        stack: &mut Stack,
        jit: &Compiler<JITModule>,
        mut callstack: CallStack<'cs>,
    ) -> Result<(), ExecError> {
        while let Some(line) = callstack.pop() {
            // println!("cs = {callstack:?}");
            let Some((token, xs)) = line.split_first() else {
                continue;
            };

            let mut optimize_push = |vals: &[Instr]| match vals {
                [] => {}
                [Instr::Literal(n), Instr::Skip, rest @ ..]
                    if (*n >= 0 && ((*n as usize) == rest.len())) => {}
                _ => {
                    callstack.push(xs);
                }
            };

            match Self::execute(funcs, stack, jit, token)? {
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
                ExecRes::RecursiveCall(newfunc) => {
                    // TODO: tailcall optimization
                    optimize_push(xs);

                    callstack.push(newfunc);
                }
            }
        }

        Ok(())
    }

    fn reset_module_and_recompile_all(&mut self) {
        // Reset the JIT
        let old = std::mem::replace(&mut self.jit, Compiler::new().unwrap());
        unsafe { old.module.free_memory() };

        let externc = self
            .jit
            .generate_signature(self.jit.module.isa().default_call_conv());

        let tail = self
            .jit
            .generate_signature(cranelift::prelude::isa::CallConv::Tail);

        for (name, f) in self.undefined_functions.drain(..) {
            self.funcmap.0.insert(
                name,
                Function {
                    code: f,
                    id: self.jit.module.declare_anonymous_function(&tail).unwrap(),
                    wrapper_id: self
                        .jit
                        .module
                        .declare_anonymous_function(&externc)
                        .unwrap(),
                },
            );
        }

        assert!(self.undefined_functions.is_empty());

        self.jit
            .compile_functions_and_wrappers(&self.funcmap)
            .unwrap();
        self.jit.module.finalize_definitions().unwrap();
    }

    /// Execute a slice of [`Token`]s representing a line of Clac++ code.
    pub fn execute_tokens(&mut self, mut line: &[Token]) -> Result<(), ExecError> {
        let mut cur_func: Option<(&String, Code)> = None;

        let mut funcs = &mut self.funcmap;
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

                        for (name, func) in &self.funcmap.0 {
                            println!(
                                "Function {name} | Wrapper @ {:?} | JIT @ {:?}",
                                self.jit.get_function(func.wrapper_id),
                                self.jit.get_function(func.id)
                            );
                        }

                        funcs = &mut self.funcmap;
                        stack = &mut self.stack;
                    }

                    match Self::execute(funcs, stack, &self.jit, &tok.clone().to_instruction())? {
                        ExecRes::Executed => (rem, None),
                        ExecRes::Skip(n) => match rem.split_at_checked(n) {
                            Some((_, rem2)) => (rem2, None),
                            None => return Err(ExecError::InvalidSkip),
                        },
                        ExecRes::RecursiveCall(f) => {
                            Self::exec_function(funcs, stack, &self.jit, vec![f])?;
                            (rem, None)
                        }
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
pub enum CompileError {
    #[error("Bad Function Definition")]
    BadFunctionDefinition,

    #[error("Top level is not allowed in Ahead of time compilation.")]
    TopLevelDisallowed,

    #[error("Cranelift module error: {0}")]
    CraneliftModuleError(#[from] ModuleError),
}

fn extract_functions(mut line: &[Token]) -> Result<HashMap<&str, Code>, CompileError> {
    let mut cur_func: Option<(&str, Code)> = None;
    let mut res: HashMap<&str, Code> = HashMap::new();

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
                return Err(CompileError::BadFunctionDefinition);
            }
            ([tok, rem @ ..], Some((nm, mut f))) => {
                f.push(tok.clone().to_instruction());
                (rem, Some((nm, f)))
            }
            ([_, ..], None) => return Err(CompileError::TopLevelDisallowed),
            ([], Some(_)) => return Err(CompileError::BadFunctionDefinition),
            ([], None) => return Ok(res),
        };
    }
}

pub fn compile_tokens(
    line: &[Token],
    isa: OwnedTargetIsa,
    object_name: String,
) -> Result<ObjectProduct, CompileError> {
    // we need to ensure that it is all functions
    let functions = extract_functions(line)?;

    let module = ObjectBuilder::new(isa, object_name, cranelift_module::default_libcall_names())?;
    let module = ObjectModule::new(module);

    Ok(module.finish())
}

pub fn compile_str(
    line: &str,
    isa: OwnedTargetIsa,
    object_name: String,
) -> Result<ObjectProduct, CompileError> {
    let parsed: Vec<Token> = line.split_whitespace().map(parse).collect();

    compile_tokens(&parsed, isa, object_name)
}
