(* analysis@home — work unit: exp-dominates-linear (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). n < 2^n for all n. *)

Require Import Arith Lia.

Lemma two_pow_pos : forall m, 1 <= 2 ^ m.
Proof. induction m; simpl; lia. Qed.
Theorem exp_dominates_linear : forall n, n < 2 ^ n.
Proof. induction n as [|m IH]; simpl. lia. pose proof (two_pow_pos m). lia. Qed.
