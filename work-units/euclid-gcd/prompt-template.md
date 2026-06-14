<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, Euclid's algorithm
(TAOCP Algorithm E). Mirror
`work-units/euclid-gcd/targets/rocq/Euclid.v`: define a fuel-bounded
`euclid fuel a b` that returns `(gcd, #division-steps)`, stepping
`(a, b) -> (b, a mod b)`. Prove both:

1. cost: `snd (euclid fuel a b) <= b` (the divisor strictly decreases);
2. correctness: `b <= fuel -> fst (euclid fuel a b) = gcd a b` (use the library
   gcd and the Euclid step lemma `gcd b (a mod b) = gcd a b`).

The canonical theorem to certify is `euclid_steps_le`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
