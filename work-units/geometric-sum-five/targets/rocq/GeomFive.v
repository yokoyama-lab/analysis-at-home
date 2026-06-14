(* analysis@home — work unit: geometric-sum-five (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 5^0 + ... + 5^(n-1) = (5^n - 1)/4. *)

Require Import Arith Lia.

Fixpoint g5 (n:nat) := match n with 0=>0 | S m => g5 m + (5^m) end.
Theorem geometric_sum_five : forall n, 4 * g5 n + 1 = 5 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
