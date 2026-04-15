mod builtins;
mod jit;
mod jit_builtins;
pub mod types;

use rustyline::error::ReadlineError;
use thiserror::Error;
use types::*;

// resolve functions so we don't need to do a costly hashmap lookup
fn resolve_funcmap(funcs: &mut FuncMap) {
    for function in &mut funcs.functions {
        if let Function::Uncompiled(f) = function {
            for token in f {
                if let Instr::FunctionCall(FuncRef::Unresolved(name)) = token
                    && let Some(resolved) = funcs.map.get(name)
                {
                    *token = Instr::FunctionCall(FuncRef::Resolved(*resolved));
                }
            }
        }
    }
}

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
                let f = match state {
                    FuncRef::Resolved(x) => &functions.functions[*x],
                    FuncRef::Unresolved(name) => match functions.map.get(name) {
                        Some(_) => unreachable!("Should have already been resolved"), // NOTE: we SHOULD be executing top level, because otherwise this token should have already been resolved.
                        None => return Err(ExecError::UnknownFunction(name.to_string())),
                    },
                };

                match f {
                    Function::Uncompiled(f) => Ok(ExecRes::RecursiveCall(f)),
                    Function::Native(f) => {
                        f(stack);
                        Ok(ExecRes::Executed)
                    }
                    Function::ArithInstr(_) => unreachable!(
                        "Tried to execute an ArithInstr as a function call, which should be impossible if this instruction was obtained from a token by token_to_instruction"
                    ),
                    Function::Compiled(f) => {
                        let new_rsp = unsafe { f(stack.rsp) };
                        stack.rsp = new_rsp;

                        Ok(ExecRes::Executed)
                    }
                }
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
                    Arith::Add => a + b,
                    Arith::Sub => a - b,
                    Arith::Mul => a * b,
                    Arith::Div => a / b,
                    Arith::Rem => a % b,
                    Arith::Lt => {
                        if a < b {
                            1
                        } else {
                            0
                        }
                    }
                    Arith::Pow => builtins::pow(a, b).ok_or(ExecError::InvalidExponent)?,
                });
                Ok(ExecRes::Executed)
            }
            Instr::Pick => {
                let conv: usize = xpop()?.try_into().map_err(|_| ExecError::InvalidPick)?;
                // let got = stack
                //     .get::<usize>(stack.len() - conv)
                //     .ok_or(ExecError::InvalidPick)?;
                let got: &mut Value = todo!();

                stack.push(*got);

                Ok(ExecRes::Executed)
            }
        }
    }

    // we have to split execute_line and this version, due to lifetime problems. When you call clac functions, it will be executing in this context, where the FunctionMap CANNOT be modified, since you cannot define functions within a function.
    fn exec_function<'cs>(
        funcs: &'cs FuncMap,
        stack: &mut Stack,
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

            match Self::execute(funcs, stack, token)? {
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
                    let len = funcs.functions.len();

                    let compiled = self.compile_function(&f).unwrap();

                    println!("JIT compiled function {} -> {:?}", name, compiled);

                    funcs = &mut self.funcmap;
                    stack = &mut self.stack;

                    // if we are re-defining a function, we should replace
                    match funcs.map.get(name) {
                        Some(idx) => {
                            funcs.functions[*idx] = Function::Compiled(compiled);
                        }
                        None => {
                            funcs.functions.push(Function::Compiled(compiled));
                            funcs.map.insert(name.to_string(), len);
                        }
                    };

                    // resolve function names to indices
                    resolve_funcmap(funcs);

                    (rem, None)
                }
                ([Token::Colon | Token::Semicolon, ..], _) => {
                    return Err(ExecError::BadFunctionDefinition);
                }
                ([tok, rem @ ..], Some((nm, mut f))) => {
                    f.push(tok.clone().token_to_instruction(funcs));
                    (rem, Some((nm, f)))
                }
                ([tok, rem @ ..], None) => {
                    match Self::execute(funcs, stack, &tok.clone().token_to_instruction(funcs))? {
                        ExecRes::Executed => (rem, None),
                        ExecRes::Skip(n) => match rem.split_at_checked(n) {
                            Some((_, rem2)) => (rem2, None),
                            None => return Err(ExecError::InvalidSkip),
                        },
                        ExecRes::RecursiveCall(f) => {
                            Self::exec_function(funcs, stack, vec![f])?;
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
pub enum ReplError {
    #[error("Execution Error: {0}")]
    ExecError(#[from] ExecError),

    #[error("Readline Error: {0}")]
    LineError(#[from] ReadlineError),

    #[error("Init error: {0}")]
    InitError(#[from] InitError),
}

/// Launch an interactive REPL on the provided ClacState.
pub fn repl(state: &mut ClacState, hide_stack: bool) -> Result<(), ReplError> {
    println!("clac++ {} by stanleymw", env!("CARGO_PKG_VERSION"),);

    let mut editor = rustyline::DefaultEditor::new()?;

    loop {
        let read = match editor.readline("clac++> ") {
            Err(ReadlineError::Eof) => return Ok(()),
            Err(ReadlineError::Interrupted) => {
                // TODO: remove
                unsafe { std::arch::asm!("int3") };
                continue;
            }
            Err(e) => return Err(e.into()),
            Ok(res) => {
                editor.add_history_entry(&res)?;
                res
            }
        };

        match state.execute_str(&read) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x.into()),
            Ok(()) => {}
        };

        if !hide_stack {
            println!("{:?}", state.stack)
        }
    }
}
