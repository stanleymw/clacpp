use std::{ffi::c_long, ops::*};

use crate::types::{
    Function::{self, *},
    Value,
};

unsafe extern "C" {
    fn syscall(num: c_long, ...) -> c_long;
}

pub const FUNCTIONS: [(&str, Function); 14] = [
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
    (
        "read8",
        Native(|stack| {
            let addr = stack.pop().expect("Stack empty on read8");
            let val = (unsafe { *(addr as *const u8) }) as Value;
            stack.push(val);
        }),
    ),
    (
        "read_native",
        Native(|stack| {
            let addr = stack.pop().expect("Stack empty on readNative");
            let val = (unsafe { *(addr as *const Value) }) as Value;
            stack.push(val);
        }),
    ),
    (
        "write8",
        Native(|stack| {
            let value: u8 = stack
                .pop()
                .expect("Stack empty on write")
                .try_into()
                .expect("trying to write8 on a value that doesn't fit in a byte");
            let addr = stack.pop().expect("Stack empty on write");

            let ptr = addr as *mut u8;
            unsafe {
                *ptr = value;
            }
        }),
    ),
    (
        "write_native",
        Native(|stack| {
            let value: Value = stack.pop().expect("Stack empty on write");
            let addr = stack.pop().expect("Stack empty on write");

            let ptr = addr as *mut Value;
            unsafe {
                *ptr = value;
            }
        }),
    ),
    (
        "syscall",
        Native(|stack| {
            let res = unsafe {
                match stack[..] {
                    [.., rax, v1, v2, v3, v4, v5, v6] => syscall(rax, v1, v2, v3, v4, v5, v6),
                    _ => panic!("syscall: Expected 7 arguments"),
                }
            };

            for _ in 0..7 {
                stack.pop();
            }

            stack.push(res);
        }),
    ),
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

            let start = stack
                .len()
                .checked_sub(start)
                .expect("Drop range start out of bounds");

            stack.drain(start..(start + amount));
        }),
    ),
    (
        "width_native",
        Native(|stack| stack.push(std::mem::size_of::<Value>() as Value)),
    ),
];
