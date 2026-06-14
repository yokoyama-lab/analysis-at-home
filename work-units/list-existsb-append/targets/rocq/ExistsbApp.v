(* analysis@home — work unit: list-existsb-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). existsb p (l1 ++ l2) = existsb p l1 || existsb p l2. *)

Require Import List Arith Lia Bool.
Import ListNotations.

Theorem list_existsb_append : forall (p:nat->bool) l1 l2, existsb p (l1 ++ l2) = existsb p l1 || existsb p l2.
Proof. intros p l1 l2. induction l1 as [|x xs IH]; simpl. reflexivity. rewrite IH, orb_assoc. reflexivity. Qed.
