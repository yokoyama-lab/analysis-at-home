(* analysis@home — work unit: heptagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 6 + 11 + ... + (5n-4) = n(5n-3)/2. *)

Require Import Arith Lia.

Fixpoint hept (n:nat) := match n with 0=>0 | S m => hept m + (5*m+1) end.
Theorem heptagonal_numbers : forall n, 2 * hept n + 3*n = 5 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
