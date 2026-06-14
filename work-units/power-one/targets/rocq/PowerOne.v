(* analysis@home — work unit: power-one (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a^1 = a. *)

Require Import Arith Lia.

Theorem power_one : forall a, a ^ 1 = a.
Proof. intro a. simpl. lia. Qed.
