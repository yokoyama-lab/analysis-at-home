<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, **Floyd's cycle
detection** (tortoise and hare). Mirror
`work-units/floyd-cycle-detection/targets/rocq/Floyd.v`:

1. define `iter f n x` (n-fold application) and prove `iter f (a+b) x = iter f a (iter f b x)`;
2. from a collision `iter f i x = iter f j x` (i<j) derive periodicity, then prove
   `floyd_meeting`: `exists m, 1 <= m /\ iter f m x = iter f (2*m) x`.

The canonical theorem to certify is `floyd_meeting`. Return only the
proof-assistant source, with no axioms / sorry / admit / postulate.
