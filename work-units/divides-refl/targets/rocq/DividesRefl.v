(* analysis@home — work unit: divides-refl (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every number divides itself. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_refl : forall a, divides a a.
Proof. intro a. exists 1. lia. Qed.
