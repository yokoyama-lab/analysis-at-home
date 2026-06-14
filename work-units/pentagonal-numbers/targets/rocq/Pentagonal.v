(* analysis@home — work unit: pentagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 4 + 7 + ... + (3n-2) = n(3n-1)/2. *)

Require Import Arith Lia.

Fixpoint pent (n:nat) := match n with 0=>0 | S m => pent m + (3*m+1) end.
Theorem pentagonal_numbers : forall n, 2 * pent n + n = 3 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
