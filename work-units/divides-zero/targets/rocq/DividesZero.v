(* analysis@home — work unit: divides-zero (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every a divides 0. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_zero : forall a, divides a 0.
Proof. intro a. exists 0. lia. Qed.
