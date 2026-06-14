(* analysis@home — work unit: decagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 9 + 17 + ... + (8n-7) = n(4n-3). *)

Require Import Arith Lia.

Fixpoint dec (n:nat) := match n with 0=>0 | S m => dec m + (8*m+1) end.
Theorem decagonal_numbers : forall n, dec n + 3*n = 4 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
