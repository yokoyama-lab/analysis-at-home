<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, the correctness of
**tail-recursive list reversal**. Mirror `work-units/rev-append-correct/targets/rocq/RevApp.v`:
define `rapp`/`fast_rev` and prove `fast_rev_correct`: `fast_rev l = rev l` (via
`rapp l acc = rev l ++ acc`). Return only the proof-assistant source, with no
axioms / sorry / admit / postulate.
