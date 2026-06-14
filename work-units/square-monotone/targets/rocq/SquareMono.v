(* analysis@home — work unit: square-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a <= b implies a^2 <= b^2. *)

Require Import Arith Lia.

Theorem square_monotone : forall a b, a <= b -> a*a <= b*b.
Proof. intros a b H. nia. Qed.
