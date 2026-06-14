(* analysis@home — work unit: karatsuba-multiplications (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 3 sub-multiplications per level  =>  M(2^k) = 3^k = n^{lg 3}. *)

Require Import Arith Lia.

Theorem karatsuba_multiplications :
  forall (M : nat -> nat),
    M 0 = 1 ->
    (forall k, M (S k) = 3 * M k) ->
    forall k, M k = 3 ^ k.
Proof.
  intros M H0 Hrec. induction k as [|m IH].
  - rewrite H0. reflexivity.
  - rewrite Hrec, IH. reflexivity.
Qed.
