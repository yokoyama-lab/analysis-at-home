(* analysis@home — work unit: nonagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 8 + 15 + ... + (7n-6) = n(7n-5)/2. *)

Require Import Arith Lia.

Fixpoint non (n:nat) := match n with 0=>0 | S m => non m + (7*m+1) end.
Theorem nonagonal_numbers : forall n, 2 * non n + 5*n = 7 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
