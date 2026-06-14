(* analysis@home — work unit: divides-antisymmetry (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If a divides b and b divides a then a = b. *)

Require Import Arith Lia.

Definition divides (a b:nat) := exists k, b = a*k.
Theorem divides_antisym : forall a b, divides a b -> divides b a -> a = b.
Proof. intros a b [k Hk] [j Hj]. destruct a as [|a'].
  - simpl in Hk; subst; reflexivity.
  - destruct k as [|k']; destruct j as [|j']; subst; simpl in *; nia. Qed.
