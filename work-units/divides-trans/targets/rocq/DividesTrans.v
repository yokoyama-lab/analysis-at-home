(* analysis@home — work unit: divides-trans (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides b and b divides c then a divides c. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_trans : forall a b c, divides a b -> divides b c -> divides a c.
Proof. intros a b c [kb Hb] [kc Hc]. exists (kb * kc). nia. Qed.
