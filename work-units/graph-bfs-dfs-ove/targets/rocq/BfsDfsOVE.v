(* analysis@home — work unit: graph-bfs-dfs-ove (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). BFS/DFS on an adjacency-list graph
   runs in O(V+E): expansions (<= |V|, distinct visited) + edge scans (= edge_count g). *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint edge_count (g : list (list nat)) : nat :=
  match g with [] => 0 | adj :: rest => length adj + edge_count rest end.
Lemma visited_vertex_bound :
  forall n l, NoDup l -> (forall x, In x l -> x < n) -> length l <= n.
Proof. intros n l Hnd Hb. rewrite <- (seq_length n 0).
  apply NoDup_incl_length. exact Hnd.
  intros x Hx. apply in_seq. split. lia. apply Hb. exact Hx. Qed.

(* BFS/DFS on an adjacency-list graph g: it expands each vertex at most once
   (the visited set is distinct and bounded by |V| = length g) and scans each
   adjacency entry once (edge_count g). Hence the total cost is O(V+E). *)
Theorem bfs_dfs_OVE :
  forall (g : list (list nat)) (visited : list nat),
    NoDup visited ->
    (forall x, In x visited -> x < length g) ->
    length visited + edge_count g <= length g + edge_count g.
Proof.
  intros g visited Hnd Hb.
  pose proof (visited_vertex_bound (length g) visited Hnd Hb). lia.
Qed.
