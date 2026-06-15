# Relaxed edge satisfies the triangle inequality

## Claim
Immediately after relaxing edge `(u,v,w)`, the **triangle inequality** holds at `v`:
> `v < length d -> nth v (relax d u v w) 0 <= nth u d 0 + w`.

This is the postcondition that makes an edge "relaxed"; Bellman-Ford / Dijkstra
establish it for every edge to certify shortest distances. With
`shortest-path-relaxation-monotone` it gives the relaxation invariant.

Reference Rocq proof (`relaxation_triangle`, axiom-free): [`targets/rocq/RelaxTri.v`](targets/rocq/RelaxTri.v).
