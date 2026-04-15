use clac_lang::{ReplError, types::*};
use clap::Parser;
use std::io::Read;

#[derive(clap::Parser)]
struct Args {
    file: Option<std::path::PathBuf>,

    /// The number of elements that the Clac Stack can store.
    #[arg(short, long, default_value_t = 1_000_000_000)]
    stack: usize,

    /// Hide the Clac Stack in the Repl
    #[arg(short = 'x', long)]
    hide_stack: bool,

    #[arg(trailing_var_arg = true)]
    _extra: Vec<String>,
}

fn main() -> Result<(), ReplError> {
    let args = Args::parse();

    let mut state: ClacState = ClacState::new(args.stack * 8)?;

    if let Some(f) = args.file {
        let mut file = std::fs::File::open(f).expect("Could not open file");

        let mut buf: String = String::new();
        let _out = file.read_to_string(&mut buf).expect("Could not read file");

        match state.execute_str(&buf) {
            Err(ExecError::Quit) => return Ok(()),
            Err(x) => return Err(x.into()),
            Ok(()) => {}
        };
    }

    clac_lang::repl(&mut state, args.hide_stack)
}
