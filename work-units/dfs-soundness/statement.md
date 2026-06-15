# DFS is sound: every visited vertex is reachable

## Claim
With `edge g u v := In v (nth u g [])` and `reach g src` the reflexive-transitive
closure of `edge` from a frontier `src`, the concrete DFS only ever visits
reachable vertices:
> if every vertex of `stack`/`visited` is reachable from `src`, then so is every
> vertex of `dfs fuel g stack visited`.

This is the **soundness** half of DFS correctness (it never invents unreachable
vertices), complementing the cost result `dfs-expansions-bound`. The invariant is
that everything ever pushed is reachable: a neighbour `w` of a reachable `v`
satisfies `edge g v w`, hence `reach g src w`. (Completeness — visiting *all*
reachable vertices — needs a termination argument and is a further effort.)

Reference Rocq proof (`dfs_sound`, axiom-free): [`targets/rocq/DfsSound.v`](targets/rocq/DfsSound.v).
