(* analysis@home — work unit: sum-of-squares (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Sum of the first n squares = n(n+1)(2n+1)/6. *)

Require Import Arith Lia.

Fixpoint sumsq (n : nat) : nat := match n with 0 => 0 | S m => sumsq m + (S m) * (S m) end.
Theorem sum_of_squares : forall n, 6 * sumsq n = n * (n + 1) * (2 * n + 1).
Proof. induction n as [|m IH]; simpl; nia. Qed.
