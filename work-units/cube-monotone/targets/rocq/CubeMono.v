(* analysis@home — work unit: cube-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). a <= b implies a^3 <= b^3. *)

Require Import Arith Lia.

Theorem cube_monotone : forall a b, a <= b -> a*a*a <= b*b*b.
Proof. intros a b H. apply Nat.mul_le_mono. apply Nat.mul_le_mono. exact H. exact H. exact H. Qed.
