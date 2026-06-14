(* analysis@home — work unit: mult-positive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). 0<a and 0<b imply 0<a*b. *)

Require Import Arith Lia.

Theorem mult_pos : forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof. intros a b Ha Hb. nia. Qed.
