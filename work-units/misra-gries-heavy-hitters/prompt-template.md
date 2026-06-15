<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the **Misra-Gries**
heavy-hitters guarantee (1982). Mirror
`work-units/misra-gries-heavy-hitters/targets/rocq/MisraGries.v`:

1. model a counter dictionary (`getc`, `total`, `incr`, decrement-all) and the
   one-pass `step`/`mg` with at most `k-1` entries;
2. prove `misra_gries`: `2 <= k -> length l < k * cnt m l -> 0 < getc m (mg k l)`,
   carrying the invariant `cnt x prefix <= getc x dict + D` and
   `total dict + k*D = length prefix`.

The canonical theorem to certify is `misra_gries`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
