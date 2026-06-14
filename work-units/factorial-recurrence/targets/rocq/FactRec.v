(* analysis@home — work unit: factorial-recurrence (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). (S n)! = (S n) * n!. *)

Require Import Arith Lia.

Fixpoint fact (n : nat) : nat := match n with 0 => 1 | S m => S m * fact m end.
Theorem factorial_recurrence : forall n, fact (S n) = S n * fact n.
Proof. reflexivity. Qed.
