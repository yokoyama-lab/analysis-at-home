(* analysis@home — work unit: ternary-mergesort-recurrence (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A 3-way divide-and-conquer with linear merge costs k*3^k on 3^k inputs (n log_3 n). *)

Require Import Arith Lia.

Theorem ternary_mergesort_recurrence :
  forall (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) <= 3 * T k + 3 ^ (S k)) -> forall k, T k <= k * 3 ^ k.
Proof. intros T H0 Hrec. induction k as [|m IH].
  - rewrite H0. simpl. lia.
  - assert (E : 3 ^ (S m) = 3 * 3 ^ m) by reflexivity. pose proof (Hrec m). nia. Qed.
