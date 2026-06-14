(* analysis@home — work unit: radix-sort-passes (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Radix sort performs d passes, each a linear distribution over n keys: d*n bucket operations. *)

Require Import Arith Lia.

Fixpoint loop (n body : nat) : nat := match n with 0 => 0 | S m => body + loop m body end.
Lemma loop_count : forall n body, loop n body = n * body.
Proof. induction n as [|m IH]; intro body; simpl; [reflexivity | rewrite IH; nia]. Qed.
Theorem radix_sort_passes : forall d n, loop d (loop n 1) = d * n.
Proof. intros d n. rewrite (loop_count n 1). rewrite (loop_count d (n * 1)). ring. Qed.
