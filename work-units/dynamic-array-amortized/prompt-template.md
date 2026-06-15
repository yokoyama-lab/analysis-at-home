<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that a **dynamic
array with table doubling** has amortized O(1) push. Mirror
`work-units/dynamic-array-amortized/targets/rocq/DynArray.v`:

1. define `da_cost n s c` (n pushes at size s, capacity c; push = 1, and when
   s = c add c copies and double the capacity);
2. prove `dynamic_array_amortized`: `da_cost n 0 1 <= 3 * n`, via the potential
   `Phi = 2*size - capacity` and the strengthened invariant
   `da_cost n s c + c <= 3*n + 2*s + 1` under `1 <= c`, `s <= c`, `c <= 2*s+1`.

The canonical theorem to certify is `dynamic_array_amortized`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
