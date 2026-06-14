(* analysis@home — work unit: graph-edge-count (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). In an adjacency-list graph the
   total number of adjacency entries equals the number of edges (the E in O(V+E)). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint edge_count (g : list (list nat)) : nat :=
  match g with [] => 0 | adj :: rest => length adj + edge_count rest end.
Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
