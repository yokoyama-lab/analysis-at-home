(* analysis@home — work unit: divides-mult-left (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides b then a divides c*b. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_mult_l : forall a b c, divides a b -> divides a (c * b).
Proof. intros a b c [k Hk]. exists (c * k). nia. Qed.
