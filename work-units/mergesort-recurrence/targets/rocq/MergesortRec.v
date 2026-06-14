(* analysis@home — work unit: mergesort-recurrence (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). T(n) <= 2T(n/2)+n  =>  T(2^k) <= k*2^k (Theta(n log n)). *)

Require Import Arith Lia.

Theorem mergesort_recurrence :
  forall (T : nat -> nat),
    T 0 = 0 ->
    (forall k, T (S k) <= 2 * T k + 2 ^ (S k)) ->
    forall k, T k <= k * 2 ^ k.
Proof.
  intros T H0 Hrec. induction k as [|m IH].
  - rewrite H0. simpl. lia.
  - assert (E : 2 ^ (S m) = 2 * 2 ^ m) by reflexivity.
    pose proof (Hrec m). nia.
Qed.
