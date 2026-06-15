<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that **run-length
encoding is lossless**. Mirror `work-units/run-length-encoding/targets/rocq/RLE.v`:
define `encode`/`decode` and prove `rle_roundtrip`: `decode (encode l) = l`.
Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
