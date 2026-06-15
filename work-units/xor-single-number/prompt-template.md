<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **XOR
single-number** trick. Mirror `work-units/xor-single-number/targets/rocq/XorSingle.v`:

1. define `xorsum = fold_right xor 0` over naturals;
2. prove it is invariant under permutation (XOR commutative/associative) and that
   `xorsum (d ++ d) = 0`;
3. prove `single_number`: `Permutation l (m :: d ++ d) -> xorsum l = m`.

The canonical theorem to certify is `single_number`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
