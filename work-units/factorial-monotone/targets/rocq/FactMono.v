(* analysis@home — work unit: factorial-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). n! <= (n+1)!. *)

Require Import Arith Lia.

Fixpoint fact (n:nat) := match n with 0 => 1 | S m => S m * fact m end.
Theorem factorial_monotone : forall n, fact n <= fact (S n).
Proof. intro n. simpl. nia. Qed.
