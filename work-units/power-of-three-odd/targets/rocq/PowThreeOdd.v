(* analysis@home — work unit: power-of-three-odd (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 3^n is odd for every n. *)

Require Import Arith Lia.

Theorem power_of_three_odd : forall n, exists k, 3 ^ n = 2 * k + 1.
Proof. induction n as [|m [k Hk]]. exists 0. reflexivity. exists (3 * k + 1). simpl. nia. Qed.
