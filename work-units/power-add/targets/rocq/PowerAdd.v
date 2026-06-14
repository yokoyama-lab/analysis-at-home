(* analysis@home — work unit: power-add (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a^(m+n) = a^m * a^n. *)

Require Import Arith Lia.

Theorem power_add : forall a m n, a ^ (m + n) = a ^ m * a ^ n.
Proof. intros a m n. induction m as [|k IH]; simpl.
  - lia.
  - rewrite IH. nia. Qed.
