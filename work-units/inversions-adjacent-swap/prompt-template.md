<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that swapping an adjacent out-of-order pair removes exactly one inversion: define the inversion count `inv` and prove `b < a -> inv (a :: b :: l) = S (inv (b :: a :: l))`. Mirror
`work-units/inversions-adjacent-swap/targets/rocq/InvSwap.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
