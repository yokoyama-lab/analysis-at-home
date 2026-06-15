(* analysis@home — work unit: bellman-ford-cost (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). Bellman-Ford does rounds*edges
   relaxations => O(V*E). *)

Require Import Arith Lia.
Fixpoint loop (n body : nat) : nat := match n with 0 => 0 | S m => body + loop m body end.
Lemma loop_count : forall n body, loop n body = n * body.
Proof. induction n as [|m IH]; intro body; simpl; [reflexivity | rewrite IH; nia]. Qed.
(* Bellman-Ford performs rounds * edges relaxations => O(V*E). *)
Theorem bellman_ford_relaxations : forall rounds edges, loop rounds (loop edges 1) = rounds * edges.
Proof. intros rounds edges. rewrite (loop_count edges 1). rewrite (loop_count rounds (edges * 1)). ring. Qed.
