(* analysis@home — work unit: mult-le-mono-both (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a<=b and c<=d imply ac<=bd. *)

Require Import Arith Lia.

Theorem mult_le_mono_both : forall a b c d, a<=b -> c<=d -> a*c <= b*d.
Proof. intros. apply Nat.mul_le_mono; assumption. Qed.
