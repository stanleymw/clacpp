mod types;
use std::{
    collections::HashMap,
    io::{self, Read, Write},
};

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
            Err(_) => Function(id.to_string()),
        },
    }
}

fn execute<'cs>(
    functions: &'cs FuncMap,
    stack: &mut ClacStack,
    token: &Token,
) -> Result<ExecRes<'cs>, ExecError> {
    match token {
        &Token::Literal(n) => {
            stack.push(n);
            Ok(ExecRes::Executed)
        }
        Token::Quit => Ok(ExecRes::Quit),
        Token::Function(name) => match functions.get(name) {
            Some(types::Function::Clac(f)) => {
                // execute_line_no_funcs(functions, stack, f.into_iter())
                Ok(ExecRes::RecursiveCall(f))
            }
            Some(types::Function::Native(f)) => {
                let res = f(stack);
                stack.push(res);

                Ok(ExecRes::Executed)
            }
            Some(types::Function::ClacOp(f)) => {
                let y = stack.pop().ok_or(ExecError::MissingArguments)?;
                let x = stack.pop().ok_or(ExecError::MissingArguments)?;

                stack.push(f(x, y));
                Ok(ExecRes::Executed)
            }
            None => Err(ExecError::UnknownFunction(name.to_string())),
        },
        &Token::Print => {
            let x = stack.pop().ok_or(ExecError::MissingArguments)?;
            println!("{x}");
            Ok(ExecRes::Executed)
        }
        &Token::Drop => {
            stack.pop().ok_or(ExecError::MissingArguments)?;
            Ok(ExecRes::Executed)
        }
        &Token::Swap => {
            let y = stack.pop().ok_or(ExecError::MissingArguments)?;
            let x = stack.pop().ok_or(ExecError::MissingArguments)?;

            stack.push(y);
            stack.push(x);

            Ok(ExecRes::Executed)
        }
        &Token::Rot => {
            let z = stack.pop().ok_or(ExecError::MissingArguments)?;
            let y = stack.pop().ok_or(ExecError::MissingArguments)?;
            let x = stack.pop().ok_or(ExecError::MissingArguments)?;

            stack.push(y);
            stack.push(z);
            stack.push(x);

            Ok(ExecRes::Executed)
        }
        &Token::If => {
            let cond = stack.pop().ok_or(ExecError::MissingArguments)?;
            if cond == 0 {
                return Ok(ExecRes::Skip(3));
            }
            Ok(ExecRes::Executed)
        }
        &Token::Skip => {
            let amt = stack.pop().ok_or(ExecError::MissingArguments)?;
            Ok(ExecRes::Skip(
                amt.try_into().map_err(|_| ExecError::InvalidSkip)?,
            ))
        }
        &Token::Pick => {
            let amt = stack.pop().ok_or(ExecError::MissingArguments)?;
            if !(amt > 0) {
                return Err(ExecError::InvalidPick);
            }
            let amt: usize = amt.try_into().unwrap();
            let got = stack
                .get(stack.len() - 1 - (amt - 1))
                .ok_or(ExecError::InvalidPick)?;

            stack.push(*got);

            Ok(ExecRes::Executed)
        }
        Token::Semicolon => Err(ExecError::BadFunctionDefinition),
        Token::Colon => Err(ExecError::BadFunctionDefinition),
    }
}

fn execute_line_nontop<'cs>(
    funcs: &'cs FuncMap,
    stack: &mut ClacStack,
    mut callstack: CallStack<'cs>,
) -> Result<LineRes, ExecError> {
    while let Some(line) = callstack.pop() {
        let Some((token, xs)) = line.split_first() else {
            continue;
        };

        match execute(funcs, stack, token) {
            Ok(ExecRes::Executed) => {
                callstack.push(xs);
            }
            Ok(ExecRes::Skip(n)) => match xs.split_at_checked(n) {
                Some((_, remain)) => {
                    callstack.push(remain);
                }
                None => return Err(ExecError::InvalidSkip),
            },
            Ok(ExecRes::Quit) => {
                return Ok(LineRes::Quit);
            }
            Ok(ExecRes::RecursiveCall(newfunc)) => {
                // TODO: remove this for tailcall optimization
                callstack.push(xs);

                callstack.push(newfunc);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    Ok(LineRes::Executed)
}

fn execute_line_toplevel<'token_line>(
    funcs: &mut FuncMap,
    stack: &mut ClacStack,
    line: &[Token],
) -> Result<LineRes, ExecError> {
    let mut cur_func: Option<(&String, Code)> = None;
    let mut it = line.iter();

    while let Some(token) = it.next() {
        match token {
            Token::Colon => {
                if let Some(_) = cur_func {
                    return Err(ExecError::BadFunctionDefinition);
                }

                let Token::Function(name) = it.next().ok_or(ExecError::BadFunctionDefinition)?
                else {
                    return Err(ExecError::BadFunctionDefinition);
                };

                cur_func = Some((name, Vec::new()))
            }
            Token::Semicolon => {
                match cur_func {
                    Some((name, f)) => {
                        funcs.insert(name.to_string(), Function::Clac(f));
                        cur_func = None;
                    }
                    None => {
                        // semicolon without starting definition
                        return Err(ExecError::BadFunctionDefinition);
                    }
                }
            }
            tok => match &mut cur_func {
                Some((_, f)) => {
                    f.push(tok.clone());
                }
                None => match execute(funcs, stack, tok)? {
                    ExecRes::Executed => {}
                    ExecRes::Skip(n) => {
                        for _ in 0..n {
                            it.next().ok_or(ExecError::InvalidSkip)?;
                        }
                    }
                    ExecRes::RecursiveCall(f) => {
                        execute_line_nontop(funcs, stack, vec![f])?;
                    }

                    ExecRes::Quit => return Ok(LineRes::Quit),
                },
            },
        }
    }

    if let Some(_) = cur_func {
        return Err(ExecError::BadFunctionDefinition);
    }

    Ok(LineRes::Executed)
}

fn exec_str(buf: &str, state: &mut ClacState) -> Result<LineRes, ExecError> {
    let parsed: Vec<Token> = buf.split_whitespace().map(parse).collect();

    execute_line_toplevel(&mut state.funcmap, &mut state.stack, &parsed)
}

fn repl(state: &mut ClacState) -> Result<(), ExecError> {
    println!("clac++ by stanleymw");

    loop {
        print!("clac++ $ ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match exec_str(&buf, state)? {
            LineRes::Executed => {}
            LineRes::Quit => {
                return Ok(());
            }
        }

        println!("{:?}", state.stack)
    }
}

fn main() -> Result<(), ExecError> {
    use std::ops::*;
    use types::Function::*;

    let mut state: ClacState = ClacState {
        stack: Vec::with_capacity(1_000_000),
        funcmap: HashMap::from_iter(
            [
                ("+", ClacOp(Add::add)),
                ("-", ClacOp(Sub::sub)),
                ("*", ClacOp(Mul::mul)),
                ("/", ClacOp(Div::div)),
                ("%", ClacOp(Rem::rem)),
                (
                    "**",
                    ClacOp(|x, y| match y.try_into() {
                        Ok(conv) => Value::pow(x, conv),
                        Err(err) => panic!("Pow error: {}", err),
                    }),
                ),
                ("<", ClacOp(|x, y| if x < y { 1 } else { 0 })),
            ]
            .into_iter()
            .map(|(name, x)| (name.to_string(), x)),
        ),
    };

    let mut args = std::env::args();
    if let Some(n) = args.nth(1) {
        let mut file = std::fs::File::open(n).expect("Could not open file");

        let mut buf: String = String::new();
        let _out = file.read_to_string(&mut buf).expect("Could not read file");

        match exec_str(&buf, &mut state)? {
            LineRes::Executed => {}
            LineRes::Quit => {
                return Ok(());
            }
        }
    }

    repl(&mut state)
}
