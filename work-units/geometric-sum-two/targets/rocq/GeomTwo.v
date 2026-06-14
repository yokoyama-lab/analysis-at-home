(* analysis@home — work unit: geometric-sum-two (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 2^0 + ... + 2^(n-1) = 2^n - 1. *)

Require Import Arith Lia.

Fixpoint sumtwo (n : nat) : nat := match n with 0 => 0 | S m => sumtwo m + 2 ^ m end.
Theorem geometric_sum_two : forall n, sumtwo n + 1 = 2 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
