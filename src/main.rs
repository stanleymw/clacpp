mod types;
use std::{
    collections::HashMap,
    io::{self, Write},
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

enum ExecRes {
    Executed,
    Skip(usize),
    Quit,
}

#[derive(Debug)]
enum ExecError {
    UnknownFunction(String),
    IfStatementCouldNotSkip,
    MissingArguments,
    InvalidSkip,
    InvalidPick,
    BadFunctionDefinition,
}

fn execute(
    functions: &FuncMap,
    stack: &mut ClacStack,
    token: &Token,
) -> Result<ExecRes, ExecError> {
    match token {
        &Token::Literal(n) => {
            stack.push(n);
            Ok(ExecRes::Executed)
        }
        &Token::Quit => Ok(ExecRes::Quit),
        Token::Function(name) => match functions.get(name) {
            Some(types::Function::Clac(f)) => {
                execute_line_no_funcs(functions, stack, f.into_iter())
            }
            // Some(types::Function::Clac(f)) => Ok(ExecRes::Executed),
            Some(types::Function::Native2(f)) => {
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
                stack.pop().ok_or(ExecError::IfStatementCouldNotSkip)?;
                stack.pop().ok_or(ExecError::IfStatementCouldNotSkip)?;
                stack.pop().ok_or(ExecError::IfStatementCouldNotSkip)?;
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

fn execute_line_no_funcs<'a>(
    funcs: &FuncMap,
    stack: &mut ClacStack,
    mut line: impl Iterator<Item = &'a Token>,
) -> Result<ExecRes, ExecError> {
    while let Some(token) = line.next() {
        match execute(funcs, stack, token) {
            Ok(ExecRes::Executed) => {}
            Ok(ExecRes::Skip(n)) => {
                for _ in 0..n {
                    if let None = line.next() {
                        return Err(ExecError::InvalidSkip);
                    }
                }
            }
            Ok(ExecRes::Quit) => {
                return Ok(ExecRes::Quit);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    Ok(ExecRes::Executed)
}

fn execute_line<'a>(
    funcs: &mut FuncMap,
    stack: &mut ClacStack,
    mut line: impl Iterator<Item = &'a Token>,
) -> Result<ExecRes, ExecError> {
    let mut cur_func: Option<(&String, Function)> = None;

    while let Some(token) = line.next() {
        match token {
            Token::Colon => {
                if let Some(_) = cur_func {
                    return Err(ExecError::BadFunctionDefinition);
                }

                let Token::Function(name) = line.next().ok_or(ExecError::BadFunctionDefinition)?
                else {
                    return Err(ExecError::BadFunctionDefinition);
                };
                cur_func = Some((name, Function::Clac(Vec::new())))
            }
            Token::Semicolon => {
                match cur_func {
                    Some((name, f)) => {
                        funcs.insert(name.to_string(), f);
                        cur_func = None;
                    }
                    None => {
                        // semicolon without starting definition
                        return Err(ExecError::BadFunctionDefinition);
                    }
                }
            }
            tok => match cur_func {
                Some((_, Function::Clac(ref mut f))) => {
                    f.push(tok.clone());
                }
                Some((_, Function::Native2(_))) => unreachable!(),
                None => match execute(funcs, stack, tok) {
                    Ok(ExecRes::Executed) => {}
                    Ok(ExecRes::Skip(n)) => {
                        for _ in 0..n {
                            if let None = line.next() {
                                return Err(ExecError::InvalidSkip);
                            }
                        }
                    }
                    Ok(ExecRes::Quit) => {
                        return Ok(ExecRes::Quit);
                    }
                    Err(e) => {
                        return Err(e);
                    }
                },
            },
        }
    }

    if let Some(_) = cur_func {
        return Err(ExecError::BadFunctionDefinition);
    }

    Ok(ExecRes::Executed)
}

fn exec_str(buf: &str, state: &mut ClacState) -> Result<ExecRes, ExecError> {
    let parsed: Vec<Token> = buf.split_whitespace().map(parse).collect();

    match execute_line(&mut state.functions, &mut state.stack, parsed.iter()) {
        Ok(ExecRes::Executed) => {
            return Ok(ExecRes::Executed);
        }
        Ok(ExecRes::Quit) => {
            return Ok(ExecRes::Quit);
        }
        Ok(ExecRes::Skip(_)) => unreachable!(),
        Err(e) => {
            return Err(e);
        }
    }
}

fn repl(state: &mut ClacState) -> Result<(), ExecError> {
    loop {
        print!("clac-rs>> ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match exec_str(&buf, state) {
            Ok(ExecRes::Executed) => {}
            Ok(ExecRes::Quit) => {
                return Ok(());
            }
            Ok(ExecRes::Skip(_)) => unreachable!(),
            Err(e) => {
                println!("{:?}", e);
                return Err(e);
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
        functions: HashMap::from_iter(
            [
                ("+", Native2(Add::add)),
                ("-", Native2(Sub::sub)),
                ("*", Native2(Mul::mul)),
                ("/", Native2(Div::div)),
                ("%", Native2(Rem::rem)),
                (
                    "**",
                    Native2(|x, y| match y.try_into() {
                        Ok(conv) => Value::pow(x, conv),
                        Err(err) => panic!("Pow error: {}", err),
                    }),
                ),
                ("<", Native2(|x, y| if x < y { 1 } else { 0 })),
            ]
            .into_iter()
            .map(|(name, x)| (name.to_string(), x)),
        ),
    };

    repl(&mut state)
}
