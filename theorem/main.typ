= Clac++ Theorem
Stanley Wang

Let $C$ be the set of all valid determinable Clac++ Instructions excluding `if` and `skip`. Determinable means that the stack delta and reach must be known at compile time.

By definition of determinable, for any $x in C$, $x$ has an associated stack delta $Delta$ in $ZZ$ and stack reach $R$ in $NN$. Intuitively, Reach is the number of values on the stack required for this instruction to execute. The stack delta is the difference between the number of elements of the new stack and old stack after executing this instruction.

We use function notation to access the delta/reach of any given $x in C$.

$Delta : C -> ZZ$

$R : C -> NN$


Lemma (true by inspection of `drop`, `rot`, etc.):
$
  forall x in C, Delta(x) >= -R(x)
$


Theorem:
For all $n in NN^+$, let
$(a_1, a_2, ... a_n) in C^n$
be an arbitrary sequence of Clac Code of length $n$:

Let $S_i$ repesent the cumulative stack delta after executing instruction $a_i$. This is
$
  S_0 = 0\
  S_i = S_(i-1) + Delta(a_i)
$
// note that for $q in NN$
// $
//   S_q = sum_(x=0)^q Delta(a_x)
// $

Let $R_i$ be the reach (relative to the beginning of the sequence) of executing instruction $a_i$.
$
  R_0 = 0\
  R_i = R(a_i) - S_(i-1)
$


Theorem statement:
$
  S_n >= - max_(0 <= i <= n) R_i
$

Proof:
By definition of $R$ and $S$,

$
  S_n + R_n = S_(n-1) + Delta(a_n) + R(a_n) - S_(n-1) \
  =
  R(a_n) + Delta(a_n)
$
And, by the lemma
$ R(a_n) + Delta(a_n) >= 0 $

Therefore
$
  S_n + R_n >= 0
  ==> S_n >= -R_n >= - max_(0 <= i <= n) R_i
$
