(* analysis@home — work unit: hexagonal-numbers (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 1 + 5 + 9 + ... + (4n-3) = n(2n-1) (the n-th hexagonal number). *)

Require Import Arith Lia.

Fixpoint hexs (n:nat) := match n with 0 => 0 | S m => hexs m + (4*m + 1) end.
Theorem hexagonal_numbers : forall n, hexs n + n = 2 * n * n.
Proof. induction n as [|m IH]; simpl; nia. Qed.
