use thiserror::Error;

use crate::{builtins, types};

pub(crate) extern "C" fn quit() {
    std::process::exit(0);
}

pub(crate) extern "C" fn pow(x: types::Value, y: types::Value) -> types::Value {
    match builtins::pow(x, y) {
        Some(res) => res,
        None => {
            eprintln!("Must pow with a non-negative exponent!");
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Error)]
#[repr(i64)]
pub(crate) enum CompiledExecutionError {
    #[error("An error occured! Clac exiting.")]
    Error,
}

pub(crate) extern "C" fn error(err: CompiledExecutionError) {
    eprintln!("{}", err);
    std::process::exit(1);
}

pub(crate) extern "C" fn print_value(val: types::Value) {
    println!("{}", val)
}
