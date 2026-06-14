<!-- Porting task (lean | agda | isabelle). The Rocq target is verified. -->

---

Formalize and prove, in <BACKEND = lean | agda | isabelle>, that union-by-rank is balanced: define uf_minsize via N(r)=2*N(r-1), N(0)=1, and prove `uf_minsize r = 2 ^ r` (so a rank-r tree has >= 2^r nodes => rank <= lg n). Mirror
`work-units/union-find-rank-bound/targets/rocq/UnionFindRank.v`.

Return only the proof-assistant source, with no axioms / sorry / admit / postulate.
