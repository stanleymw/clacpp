use clac_lang::types::*;
use clap::Parser;
use std::io::{self, Read, Write};

fn repl(state: &mut ClacState, hide_stack: bool) -> Result<(), ExecError> {
    println!("clac++ by stanleymw");

    loop {
        print!("clac++> ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match state.execute_str(&buf) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x),
            Ok(()) => {}
        };

        if !hide_stack {
            println!("{:?}", state.stack)
        }
    }
}

#[derive(clap::Parser)]
struct Args {
    file: Option<std::path::PathBuf>,

    /// The number of elements that will have space pre-allocate for on the Clac Stack
    #[arg(short, long, default_value_t = 1_000_000)]
    stack: usize,

    /// Hide the Clac Stack in the Repl
    #[arg(short = 'x', long)]
    hide_stack: bool,

    #[arg(trailing_var_arg = true)]
    _extra: Vec<String>,
}

fn main() -> Result<(), ExecError> {
    let args = Args::parse();

    let mut state: ClacState = Default::default();
    state.stack.reserve(args.stack);

    if let Some(f) = args.file {
        let mut file = std::fs::File::open(f).expect("Could not open file");

        let mut buf: String = String::new();
        let _out = file.read_to_string(&mut buf).expect("Could not read file");

        match state.execute_str(&buf) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x),
            Ok(()) => {}
        };
    }

    repl(&mut state, args.hide_stack)
}
