(* analysis@home — work unit: factorial-positive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The factorial of any n is at least 1. *)

Require Import Arith Lia.

Fixpoint fact (n : nat) : nat := match n with 0 => 1 | S m => S m * fact m end.
Theorem factorial_positive : forall n, 1 <= fact n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
