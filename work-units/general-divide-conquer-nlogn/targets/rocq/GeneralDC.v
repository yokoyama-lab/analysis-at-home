(* analysis@home — work unit: general-divide-conquer-nlogn (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Splitting into b parts of size n/b with linear merge gives T(b^k) <= k*b^k (n log_b n); subsumes mergesort (b=2) and ternary (b=3). *)

Require Import Arith Lia.

Theorem general_dc_nlogn :
  forall (b : nat) (T : nat -> nat), T 0 = 0 -> (forall k, T (S k) <= b * T k + b ^ (S k)) -> forall k, T k <= k * b ^ k.
Proof. intros b T H0 Hrec. induction k as [|m IH].
  - rewrite H0. lia.
  - assert (E : b ^ (S m) = b * b ^ m) by reflexivity. pose proof (Hrec m). nia. Qed.
