(* analysis@home — work unit: power-base-one (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). One raised to any power is one. *)

Require Import Arith Lia.
Theorem power_base_one : forall n, 1 ^ n = 1.
Proof. induction n as [|m IH]; simpl. reflexivity. rewrite IH. lia. Qed.
