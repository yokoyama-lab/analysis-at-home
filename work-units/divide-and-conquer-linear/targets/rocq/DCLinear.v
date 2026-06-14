(* analysis@home — work unit: divide-and-conquer-linear (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). T(n) <= T(n/2)+n  =>  T(2^k) <= 2^(k+1) (linear). *)

Require Import Arith Lia.

Theorem dc_linear_recurrence :
  forall (T : nat -> nat),
    T 0 = 0 ->
    (forall k, T (S k) <= T k + 2 ^ (S k)) ->
    forall k, T k <= 2 ^ (S k).
Proof.
  intros T H0 Hrec. induction k as [|m IH].
  - rewrite H0. simpl. lia.
  - assert (E : 2 ^ (S (S m)) = 2 * 2 ^ (S m)) by reflexivity.
    pose proof (Hrec m). lia.
Qed.
