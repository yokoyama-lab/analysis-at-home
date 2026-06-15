# Union-Find: path compression gives one-step find

## Claim
Path compression repoints a node directly at its set's root. Modelling the parent
array update `upd p x r` (set `p[x] := r`), we prove that afterwards `find` reaches
the root in **one step**:
> `x < length p -> find 1 (upd p x r) x = r`.

This is the mechanism by which path compression accelerates subsequent `find`s:
repeated queries become O(1) once the path is flattened. With `union-find-rank-bound`
(rank ≤ lg n) and `union-find-find-root`/`-idempotent` (find correctness) this
captures the practical efficiency of union-find.

## On the inverse-Ackermann bound
The full result — that `m` operations with **union by rank + path compression** run
in `O(m · α(n))` amortized (Tarjan 1975) via the potential method — is one of the
hardest classical analyses to formalize (a published multi-month effort, e.g.
Charguéraud–Pottier). It is deliberately **out of scope** here; this unit captures
the per-operation compression mechanism, the tractable verified core.

Reference Rocq proof (`path_compression_one_step`, axiom-free): [`targets/rocq/PathCompression.v`](targets/rocq/PathCompression.v).
