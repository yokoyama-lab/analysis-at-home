(* analysis@home — work unit: n-le-factorial (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every n is at most n!. *)

Require Import Arith Lia.

Fixpoint fact (n : nat) : nat := match n with 0 => 1 | S m => S m * fact m end.
Lemma factorial_positive : forall n, 1 <= fact n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
Theorem n_le_factorial : forall n, n <= fact n.
Proof. induction n as [|m IH]; simpl. lia.
  assert (1 <= fact m) by (apply factorial_positive). nia. Qed.
