(* analysis@home — work unit: one-divides (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 divides every a. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem one_divides : forall a, divides 1 a.
Proof. intro a. exists a. lia. Qed.
