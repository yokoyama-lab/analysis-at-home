(* analysis@home — work unit: divides-add (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides b and c then a divides b+c. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_add : forall a b c, divides a b -> divides a c -> divides a (b + c).
Proof. intros a b c [kb Hb] [kc Hc]. exists (kb + kc). nia. Qed.
