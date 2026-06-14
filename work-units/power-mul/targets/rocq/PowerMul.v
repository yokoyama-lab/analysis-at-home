(* analysis@home — work unit: power-mul (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a^(m*n) = (a^n)^m. *)

Require Import Arith Lia.

Lemma power_add : forall a m n, a ^ (m + n) = a ^ m * a ^ n.
Proof. intros a m n. induction m as [|k IH]; simpl; [lia | rewrite IH; nia]. Qed.
Theorem power_mul : forall a m n, a ^ (m * n) = (a ^ n) ^ m.
Proof. intros a m n. induction m as [|k IH].
  - reflexivity.
  - rewrite Nat.mul_succ_l, power_add, IH. simpl. nia. Qed.
