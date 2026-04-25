use std::sync::LazyLock;

use ahash::AHashMap;

use crate::types::{ArithOp, Instr, MemOp, Value};

pub(crate) unsafe extern "C" fn syscall(
    n: Value,
    a1: Value,
    a2: Value,
    a3: Value,
    a4: Value,
    a5: Value,
    a6: Value,
) -> Value {
    unsafe {
        sc::syscall6(
            n as usize,
            a1 as usize,
            a2 as usize,
            a3 as usize,
            a4 as usize,
            a5 as usize,
            a6 as usize,
        ) as i64
    }
}

pub(crate) fn pow(x: Value, y: Value) -> Option<Value> {
    Some(x.wrapping_pow(y.try_into().ok()?))
}

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
