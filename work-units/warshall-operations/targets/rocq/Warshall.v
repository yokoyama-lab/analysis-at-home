(* analysis@home — work unit: warshall-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Floyd-Warshall's three nested loops perform V^3 relaxations. *)

Require Import Arith Lia.

Fixpoint loop (n body : nat) : nat := match n with 0 => 0 | S m => body + loop m body end.
Lemma loop_count : forall n body, loop n body = n * body.
Proof. induction n as [|m IH]; intro body; simpl; [reflexivity | rewrite IH; nia]. Qed.
Theorem warshall_operations : forall v, loop v (loop v (loop v 1)) = v * v * v.
Proof. intro v. rewrite (loop_count v 1). rewrite (loop_count v (v * 1)). rewrite (loop_count v (v * (v * 1))). ring. Qed.
