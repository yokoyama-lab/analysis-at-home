<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that **binary
representation round-trips**. Mirror
`work-units/binary-rep-roundtrip/targets/rocq/Bits.v`: define `to_bits`/`from_bits`
and prove `bits_roundtrip`: `n <= fuel -> from_bits (to_bits fuel n) = n`. Return
only the proof-assistant source, with no axioms / sorry / admit / postulate.
