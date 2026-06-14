(* analysis@home — work unit: geometric-sum-four (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 4^0 + ... + 4^(n-1) = (4^n - 1)/3. *)

Require Import Arith Lia.

Fixpoint s4 (n:nat) := match n with 0 => 0 | S m => s4 m + 4 ^ m end.
Theorem geometric_sum_four : forall n, 3 * s4 n + 1 = 4 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
