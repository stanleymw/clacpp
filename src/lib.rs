mod builtins;
pub mod types;

use types::*;

// resolve functions so we don't need to do a costly hashmap lookup
fn resolve_funcmap(funcs: &mut FuncMap) {
    for function in &mut funcs.functions {
        if let Function::Clac(f) = function {
            for token in f {
                if let Token::FunctionCall(FunctionRef::Unresolved(name)) = token
                    && let Some(resolved) = funcs.map.get(name)
                {
                    *token = Token::FunctionCall(FunctionRef::Resolved(*resolved));
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
            Err(_) => FunctionCall(FunctionRef::Unresolved(id.to_string())),
        },
    }
}

impl ClacState {
    fn execute<'cs>(
        functions: &'cs FuncMap,
        stack: &mut ClacStack,
        token: &Token,
    ) -> Result<ExecRes<'cs>, ExecError> {
        match (stack.as_mut_slice(), token) {
            (_, Token::Literal(n)) => {
                stack.push(*n);
                Ok(ExecRes::Executed)
            }
            (_, Token::Quit) => Err(ExecError::Quit),
            (_, Token::FunctionCall(state)) => {
                let f = match state {
                    FunctionRef::Resolved(x) => &functions.functions[*x],
                    FunctionRef::Unresolved(name) => match functions.map.get(name) {
                        Some(x) => &functions.functions[*x], // NOTE: we SHOULD be executing top level, because otherwise this token should have already been resolved.
                        None => return Err(ExecError::UnknownFunction(name.to_string())),
                    },
                };

                match f {
                    Function::Clac(f) => Ok(ExecRes::RecursiveCall(f)),
                    Function::Native(f) => {
                        f(stack);
                        Ok(ExecRes::Executed)
                    }
                    Function::ClacOp(f) => {
                        let y = stack.pop().ok_or(ExecError::MissingArguments)?;
                        let x = stack.pop().ok_or(ExecError::MissingArguments)?;

                        stack.push(f(x, y));
                        Ok(ExecRes::Executed)
                    }
                }
            }

            ([.., x], Token::Print) => {
                println!("{x}");
                stack.pop();
                Ok(ExecRes::Executed)
            }
            ([.., _], Token::Drop) => {
                stack.pop().expect("unreachable");
                Ok(ExecRes::Executed)
            }
            ([.., x, y], Token::Swap) => {
                std::mem::swap(x, y);
                Ok(ExecRes::Executed)
            }
            ([.., x, y, z], Token::Rot) => {
                (*x, *y, *z) = (*y, *z, *x);
                Ok(ExecRes::Executed)
            }
            ([.., 0], Token::If) => {
                stack.pop().unwrap();

                Ok(ExecRes::Skip(3))
            }
            ([.., _], Token::If) => {
                stack.pop().unwrap();

                Ok(ExecRes::Executed)
            }
            ([.., n], Token::Skip) => {
                let n = *n;
                stack.pop();
                Ok(ExecRes::Skip(
                    n.try_into().map_err(|_| ExecError::InvalidSkip)?,
                ))
            }
            ([.., n], Token::Pick) if (*n > 0) => {
                let conv: usize = (*n).try_into().unwrap();
                stack.pop();
                let got = stack
                    .get::<usize>(stack.len() - conv)
                    .ok_or(ExecError::InvalidPick)?;

                stack.push(*got);

                Ok(ExecRes::Executed)
            }
            (
                _,
                Token::Swap
                | Token::Print
                | Token::Drop
                | Token::Rot
                | Token::If
                | Token::Pick
                | Token::Skip,
            ) => Err(ExecError::MissingArguments),
            (_, Token::Semicolon) => unreachable!(),
            (_, Token::Colon) => unreachable!(),
        }
    }

    // we have to split execute_line and this version, due to lifetime problems. When you call clac functions, it will be executing in this context, where the FunctionMap CANNOT be modified, since you cannot define functions within a function.
    fn execute_line_nontop<'cs>(
        funcs: &'cs FuncMap,
        stack: &mut ClacStack,
        mut callstack: CallStack<'cs>,
    ) -> Result<(), ExecError> {
        while let Some(line) = callstack.pop() {
            // println!("cs = {callstack:?}");
            let Some((token, xs)) = line.split_first() else {
                continue;
            };

            let mut optimize_push = |vals: &[Token]| match vals {
                [] => {}
                [Token::Literal(n), Token::Skip, rest @ ..]
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

        let funcs = &mut self.funcmap;
        let stack = &mut self.stack;

        loop {
            (line, cur_func) = match (line, cur_func) {
                (
                    [
                        Token::Colon,
                        Token::FunctionCall(FunctionRef::Unresolved(name)),
                        rem @ ..,
                    ],
                    None,
                ) => (rem, Some((name, Vec::new()))),
                ([Token::Semicolon, rem @ ..], Some((name, f))) => {
                    let len = funcs.functions.len();

                    // if we are re-defining a function, we should replace
                    match funcs.map.get(name) {
                        Some(idx) => {
                            funcs.functions[*idx] = Function::Clac(f);
                        }
                        None => {
                            funcs.functions.push(Function::Clac(f));
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
                    f.push(tok.clone());
                    (rem, Some((nm, f)))
                }
                ([tok, rem @ ..], None) => match Self::execute(funcs, stack, tok)? {
                    ExecRes::Executed => (rem, None),
                    ExecRes::Skip(n) => match rem.split_at_checked(n) {
                        Some((_, rem2)) => (rem2, None),
                        None => return Err(ExecError::InvalidSkip),
                    },
                    ExecRes::RecursiveCall(f) => {
                        Self::execute_line_nontop(funcs, stack, vec![f])?;
                        (rem, None)
                    }
                },
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

impl Default for ClacState {
    fn default() -> Self {
        ClacState {
            stack: Vec::new(),
            funcmap: name_func_pair_to_funcmap(builtins::FUNCTIONS),
        }
    }
}
