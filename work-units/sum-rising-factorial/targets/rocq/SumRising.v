(* analysis@home — work unit: sum-rising-factorial (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Sum of i(i+1)(i+2) = n(n+1)(n+2)(n+3)/4 (telescoping). *)

Require Import Arith Lia.

Fixpoint srf (n:nat) := match n with 0 => 0 | S m => srf m + (S m)*(S m + 1)*(S m + 2) end.
Theorem sum_rising_factorial : forall n, 4 * srf n = n*(n+1)*(n+2)*(n+3).
Proof. induction n as [|m IH]; simpl; nia. Qed.
