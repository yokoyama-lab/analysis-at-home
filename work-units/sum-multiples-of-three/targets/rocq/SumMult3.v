(* analysis@home — work unit: sum-multiples-of-three (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 3 + 6 + ... + 3n = 3n(n+1)/2. *)

Require Import Arith Lia.

Fixpoint sm3 (n:nat) := match n with 0 => 0 | S m => sm3 m + 3*(S m) end.
Theorem sum_multiples_of_three : forall n, 2 * sm3 n = 3 * (n * (n + 1)).
Proof. induction n as [|m IH]; simpl; nia. Qed.
