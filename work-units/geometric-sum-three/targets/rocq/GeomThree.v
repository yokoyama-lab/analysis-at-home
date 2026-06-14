(* analysis@home — work unit: geometric-sum-three (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The radix-3 geometric series sums to (3^n - 1)/2. *)

Require Import Arith Lia.

Fixpoint sumthree (n : nat) : nat := match n with 0 => 0 | S m => sumthree m + 3 ^ m end.
Theorem geometric_sum_three : forall n, 2 * sumthree n + 1 = 3 ^ n.
Proof. induction n as [|m IH]; simpl; lia. Qed.
