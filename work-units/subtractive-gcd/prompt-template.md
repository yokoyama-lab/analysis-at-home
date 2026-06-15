<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **subtractive GCD**
(Euclid's original, subtraction-only). Mirror
`work-units/subtractive-gcd/targets/rocq/SubGcd.v`: define `subgcd` and prove
`subgcd_correct`: `a + b <= fuel -> subgcd fuel a b = Nat.gcd a b`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
