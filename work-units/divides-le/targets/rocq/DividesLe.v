(* analysis@home — work unit: divides-le (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides a positive b, then a <= b. *)

Require Import Arith Lia.

Definition divides (a b : nat) := exists k, b = a * k.
Theorem divides_le : forall a b, divides a b -> 0 < b -> a <= b.
Proof. intros a b [k Hk] Hpos. destruct k as [|k']; subst; simpl in *; nia. Qed.
