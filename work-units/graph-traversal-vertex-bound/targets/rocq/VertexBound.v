(* analysis@home — work unit: graph-traversal-vertex-bound (Rocq target). VERIFIED
   (Print Assumptions: closed under the global context). The pigeonhole bound behind
   the O(V) term of BFS/DFS: a visited set of distinct vertices below n has size <= n. *)

Require Import List Arith Lia.
Import ListNotations.
(* The visited-set bound behind the O(V) term of graph traversal: a set of
   distinct vertices, each below n = |V|, has at most n elements. So a DFS/BFS
   that marks each vertex at most once performs at most |V| expansions. *)
Theorem visited_vertex_bound :
  forall n l, NoDup l -> (forall x, In x l -> x < n) -> length l <= n.
Proof.
  intros n l Hnd Hb.
  rewrite <- (seq_length n 0).
  apply NoDup_incl_length. exact Hnd.
  intros x Hx. apply in_seq. split. lia. apply Hb. exact Hx.
Qed.
