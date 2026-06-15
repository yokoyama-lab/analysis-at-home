# Edge relaxation only decreases distances

## Claim
The relaxation step of Bellman-Ford / Dijkstra, `relax d u v w := dist[v] := min(dist[v], dist[u]+w)`, is **monotone**: it never increases any distance.
> `forall i, nth i (relax d u v w) 0 <= nth i d 0`.

This is the core invariant of all shortest-path relaxation algorithms (distances
only improve), underlying their termination and correctness.

Reference Rocq proof (`relaxation_monotone`, axiom-free): [`targets/rocq/RelaxMono.v`](targets/rocq/RelaxMono.v).
