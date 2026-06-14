(* analysis@home — work unit: triangular-sum-square (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). T_n + T_{n+1} = (n+1)^2. *)

Require Import Arith Lia.

Fixpoint tri (n:nat) := match n with 0 => 0 | S m => tri m + S m end.
Theorem triangular_sum_square : forall n, tri n + tri (S n) = (S n) * (S n).
Proof. induction n as [|m IH]; simpl in *; nia. Qed.
