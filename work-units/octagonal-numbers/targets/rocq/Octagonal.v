(* analysis@home — work unit: octagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 7 + 13 + ... + (6n-5) = n(3n-2). *)

Require Import Arith Lia.

Fixpoint oct (n:nat) := match n with 0=>0 | S m => oct m + (6*m+1) end.
Theorem octagonal_numbers : forall n, oct n + 2*n = 3 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
