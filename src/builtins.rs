use std::{ffi::c_long, sync::LazyLock};

use ahash::AHashMap;

use crate::types::{ArithOp, Function::*, Instr, MemOp, Value};

unsafe extern "C" {
    pub(crate) fn syscall(num: c_long, ...) -> c_long;
}

pub(crate) fn pow(x: Value, y: Value) -> Option<Value> {
    Some(x.wrapping_pow(y.try_into().ok()?))
}

/*
    (
        "drop_range",
        Native(|stack| {
            let amount: usize = stack
                .pop()
                .expect("Stack empty on dropRange")
                .try_into()
                .expect("Drop amount must be nonnegative");
            let start: usize = stack
                .pop()
                .expect("Stack empty on dropRange")
                .try_into()
                .expect("Drop start must be nonnegative");
            todo!()
            // let start = stack
            //     .len()
            //     .checked_sub(start)
            //     .expect("Drop range start out of bounds");

            // stack.drain(start..(start + amount));
        }),
    ),

*/

pub static FUNCTIONS: LazyLock<AHashMap<&str, Instr>> = LazyLock::new(|| {
    AHashMap::from([
        // arith
        ("+", Instr::Arith(ArithOp::Add)),
        ("-", Instr::Arith(ArithOp::Sub)),
        ("*", Instr::Arith(ArithOp::Mul)),
        ("/", Instr::Arith(ArithOp::Div)),
        ("%", Instr::Arith(ArithOp::Rem)),
        ("<", Instr::Arith(ArithOp::Lt)),
        ("**", Instr::Arith(ArithOp::Pow)),
        // mem
        ("read8", Instr::Mem(MemOp::Read8)),
        ("write8", Instr::Mem(MemOp::Write8)),
        ("read_native", Instr::Mem(MemOp::ReadNative)),
        ("write_native", Instr::Mem(MemOp::WriteNative)),
        ("width_native", Instr::Mem(MemOp::WidthNative)),
        // side effects
        ("syscall", Instr::Syscall),
        // stack
        ("drop_range", Instr::DropRange),
    ])
});
