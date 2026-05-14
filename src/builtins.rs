use std::sync::LazyLock;

use ahash::AHashMap;

use crate::types::{ArithOp, BasicBlockInstr, Instr, MemOp, Value};

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
        ("+", BasicBlockInstr::Arith(ArithOp::Add).into()),
        ("-", BasicBlockInstr::Arith(ArithOp::Sub).into()),
        ("*", BasicBlockInstr::Arith(ArithOp::Mul).into()),
        ("/", BasicBlockInstr::Arith(ArithOp::Div).into()),
        ("%", BasicBlockInstr::Arith(ArithOp::Rem).into()),
        ("<", BasicBlockInstr::Arith(ArithOp::Lt).into()),
        ("**", BasicBlockInstr::Arith(ArithOp::Pow).into()),
        // mem
        ("read8", BasicBlockInstr::Mem(MemOp::Read8).into()),
        ("write8", BasicBlockInstr::Mem(MemOp::Write8).into()),
        (
            "read_native",
            BasicBlockInstr::Mem(MemOp::ReadNative).into(),
        ),
        (
            "write_native",
            BasicBlockInstr::Mem(MemOp::WriteNative).into(),
        ),
        (
            "width_native",
            BasicBlockInstr::Mem(MemOp::WidthNative).into(),
        ),
        // side effects
        ("syscall", BasicBlockInstr::Syscall.into()),
        // stack
        ("drop_range", BasicBlockInstr::BadDropRange.into()),
    ])
});
