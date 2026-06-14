(* analysis@home — work unit: power-of-product (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). (a*b)^n = a^n * b^n. *)

Require Import Arith Lia.

Theorem power_mul_base : forall a b n, (a * b) ^ n = a ^ n * b ^ n.
Proof. intros a b n. induction n as [|k IH]; simpl. lia. rewrite IH. nia. Qed.
