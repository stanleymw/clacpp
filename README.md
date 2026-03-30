# **Clac++**
This is the reference implementation for **Clac++**, which is a simple stack-based postfix (reverse polish notation) calculator/programming language. It supports programmer-defined functions, control flow and unrestricted recursion.

```console
$ cat print2.clac
: dup 1 pick ;
: print2 dup print dup print ;

25 10 * 5 / print2

quit
$ ./clac++ print2.clac
50
50
```

It is inspired by and (aims to be) backward compatible with the "Clac" language from Carnegie Mellon University's 15-122 programming class.

Additionally, Clac++ allows for arbitrary syscalls, and reads/writes to arbitrary memory addresses.

## Clac++26 Standard
The current (draft) Clac++26 standard allows for size of integer values on the Clac Stack to be implementation defined.

Implementations must provide a builtin function `width_native`, which must push the size of a Clac Value (in bits) to the stack. The native width on this implementation is _64 bits_, to allow for representing pointers on a 64-bit system.
