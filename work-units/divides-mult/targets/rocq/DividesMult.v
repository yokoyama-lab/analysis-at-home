(* analysis@home — work unit: divides-mult (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides b then a divides b*c. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_mult_r : forall a b c, divides a b -> divides a (b * c).
Proof. intros a b c [kb Hb]. exists (kb * c). nia. Qed.
