(* analysis@home — work unit: mult-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a <= b implies a*c <= b*c. *)

Require Import Arith Lia.

Theorem mult_monotone : forall a b c, a <= b -> a*c <= b*c.
Proof. intros a b c H. nia. Qed.
