(* analysis@home — work unit: div-mod-identity (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The Euclidean division identity for a nonzero divisor. *)

Require Import Arith Lia.
Theorem div_mod_identity : forall a b, b <> 0 -> a = b * (a / b) + a mod b.
Proof. intros a b H. apply Nat.div_mod. exact H. Qed.
