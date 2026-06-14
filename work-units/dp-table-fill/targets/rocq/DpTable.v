(* analysis@home — work unit: dp-table-fill (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Filling an n-by-m dynamic-programming table (LCS, edit distance, matrix chain) costs n*m cell updates. *)

Require Import Arith Lia.

Fixpoint loop (n body : nat) : nat := match n with 0 => 0 | S m => body + loop m body end.
Lemma loop_count : forall n body, loop n body = n * body.
Proof. induction n as [|m IH]; intro body; simpl; [reflexivity | rewrite IH; nia]. Qed.
Theorem dp_table_fill : forall n m, loop n (loop m 1) = n * m.
Proof. intros n m. rewrite (loop_count m 1). rewrite (loop_count n (m * 1)). ring. Qed.
