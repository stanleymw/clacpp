use clac_lang::types::*;
use clap::Parser;
use cranelift::prelude::{Configurable, isa::lookup};
use std::io::Read;

#[derive(clap::Parser)]
#[clap(version)]
pub struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand)]
enum Commands {
    #[clap(alias = "c")]
    Compile { file: std::path::PathBuf },

    #[clap(alias = "r")]
    Run {
        file: Option<std::path::PathBuf>,

        /// The number of elements that the Clac Stack can store.
        #[arg(short, long, default_value_t = 1_000_000_000)]
        stack: usize,

        /// Hide the Clac Stack in the Repl
        #[arg(short = 'x', long)]
        hide_stack: bool,

        #[arg(trailing_var_arg = true)]
        _extra: Vec<String>,
    },
}

fn main() -> Result<(), ReplError> {
    let args = Cli::parse();

    match args.command {
        Commands::Compile { file } => {
            let mut file = std::fs::File::open(file).expect("Could not open file");

            let mut buf: String = String::new();
            let _out = file.read_to_string(&mut buf).expect("Could not read file");

            let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
                panic!("host machine is not supported: {msg}");
            });

            let mut flag_builder = cranelift::prelude::settings::builder();

            flag_builder.set("opt_level", "speed").unwrap();
            flag_builder.set("enable_alias_analysis", "true").unwrap();
            flag_builder.set("preserve_frame_pointers", "true").unwrap();

            let isa = isa_builder
                .finish(cranelift::prelude::settings::Flags::new(flag_builder))
                .unwrap();

            let out = clac_lang::compile_str(&buf, isa, "out").unwrap();

            let file = std::fs::File::create("clac_out.o").unwrap();

            out.object.write_stream(file).unwrap();

            Ok(())
        }
        Commands::Run {
            file,
            stack,
            hide_stack,
            _extra,
        } => {
            let mut state: ClacState = ClacState::new(stack * 8)?;

            if let Some(f) = file {
                let mut file = std::fs::File::open(f).expect("Could not open file");

                let mut buf: String = String::new();
                let _out = file.read_to_string(&mut buf).expect("Could not read file");

                match state.execute_str(&buf) {
                    Err(ExecError::Quit) => return Ok(()),
                    Err(x) => return Err(x.into()),
                    Ok(()) => {}
                };
            }

            state.repl(hide_stack)
        }
    }
}
