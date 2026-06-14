(* analysis@home — work unit: two-pow-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 2^n <= 2^(S n). *)

Require Import Arith Lia.

Lemma two_pow_positive : forall n, 1 <= 2 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
Theorem two_pow_le_succ : forall n, 2 ^ n <= 2 ^ (S n).
Proof. intro n. simpl. pose proof (two_pow_positive n). lia. Qed.
