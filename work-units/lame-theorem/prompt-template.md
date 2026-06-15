<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, **Lamé's theorem**
(TAOCP Vol. 2 §4.5.3): consecutive Fibonacci numbers are the worst case of the
Euclidean algorithm. Mirror `work-units/lame-theorem/targets/rocq/Lame.v`:

1. define `fib` and a fuel-bounded step counter `steps fuel a b` that counts the
   `(a,b) -> (b, a mod b)` division steps;
2. prove `lame`: for `b < fuel`, `b < a`, `steps fuel a b = n` and `1 <= n`,
   `fib (S n) <= b /\ fib (S (S n)) <= a`.

The canonical theorem to certify is `lame`. Use induction on `fuel` and the fact
that `a > b` forces the quotient `a / b >= 1`, so `a >= b + a mod b`. Return only
the proof-assistant source, with no axioms / sorry / admit / postulate.
