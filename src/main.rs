mod builtins;
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
    match (stack.as_mut_slice(), token) {
        (_, Token::Literal(n)) => {
            stack.push(*n);
            Ok(ExecRes::Executed)
        }
        (_, Token::Quit) => Err(ExecError::Quit),
        (_, Token::Function(name)) => match functions.get(name) {
            Some(types::Function::Clac(f)) => Ok(ExecRes::RecursiveCall(f)),
            Some(types::Function::Native(f)) => {
                f(stack);
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

        match execute(funcs, stack, token)? {
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

fn execute_line_toplevel(
    funcs: &mut FuncMap,
    stack: &mut ClacStack,
    mut line: &[Token],
) -> Result<(), ExecError> {
    let mut cur_func: Option<(&String, Code)> = None;

    loop {
        (line, cur_func) = match (&line[..], cur_func) {
            ([Token::Colon, Token::Function(name), rem @ ..], None) => {
                (rem, Some((name, Vec::new())))
            }
            ([Token::Semicolon, rem @ ..], Some((name, f))) => {
                funcs.insert(name.to_string(), Function::Clac(f));
                (rem, None)
            }
            ([Token::Colon | Token::Semicolon, ..], _) => {
                return Err(ExecError::BadFunctionDefinition);
            }
            ([tok, rem @ ..], Some((nm, mut f))) => {
                f.push(tok.clone());
                (rem, Some((nm, f)))
            }
            ([tok, rem @ ..], None) => match execute(funcs, stack, tok)? {
                ExecRes::Executed => (rem, None),
                ExecRes::Skip(n) => match rem.split_at_checked(n) {
                    Some((_, rem2)) => (rem2, None),
                    None => return Err(ExecError::InvalidSkip),
                },
                ExecRes::RecursiveCall(f) => {
                    execute_line_nontop(funcs, stack, vec![f])?;
                    (rem, None)
                }
            },
            ([], Some(_)) => return Err(ExecError::BadFunctionDefinition),
            ([], None) => return Ok(()),
        };
    }
}

fn exec_str(buf: &str, state: &mut ClacState) -> Result<(), ExecError> {
    let parsed: Vec<Token> = buf.split_whitespace().map(parse).collect();

    execute_line_toplevel(&mut state.funcmap, &mut state.stack, &parsed)
}

fn repl(state: &mut ClacState) -> Result<(), ExecError> {
    println!("clac++ by stanleymw");

    loop {
        print!("clac++> ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match exec_str(&buf, state) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x),
            Ok(()) => {}
        };

        println!("{:?}", state.stack)
    }
}

fn main() -> Result<(), ExecError> {
    let mut state: ClacState = ClacState {
        stack: Vec::with_capacity(1_000_000),
        funcmap: HashMap::from_iter(
            builtins::FUNCTIONS
                .into_iter()
                .map(|(name, x)| (name.to_string(), x)),
        ),
    };

    let mut args = std::env::args();
    if let Some(n) = args.nth(1) {
        let mut file = std::fs::File::open(n).expect("Could not open file");

        let mut buf: String = String::new();
        let _out = file.read_to_string(&mut buf).expect("Could not read file");

        match exec_str(&buf, &mut state) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x),
            Ok(()) => {}
        };
    }

    repl(&mut state)
}
