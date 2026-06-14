<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that swapping an adjacent out-of-order pair anywhere removes one inversion: prove `b < a -> inv (pre ++ a :: b :: post) = S (inv (pre ++ b :: a :: post))` (use additivity of the inversion count over ++). Mirror
`work-units/inversions-swap-anywhere/targets/rocq/InvSwapAnywhere.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
