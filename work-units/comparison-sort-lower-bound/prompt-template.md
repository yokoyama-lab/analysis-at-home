<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the
**comparison-sort lower bound** (TAOCP Vol. 3 §5.3.1). Mirror
`work-units/comparison-sort-lower-bound/targets/rocq/CompSortLB.v`:

1. define binary trees with `leaves` and `height`;
2. prove `leaves t <= 2 ^ height t`;
3. prove `comparison_sort_lower_bound`: `fact n <= leaves t -> log2 (fact n) <= height t`
   (monotonicity of `log2` plus `log2 (2^h) = h`).

The canonical theorem to certify is `comparison_sort_lower_bound`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
