(* analysis@home — work unit: list-forallb-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). forallb p (l1 ++ l2) = forallb p l1 && forallb p l2. *)

Require Import List Arith Lia Bool.
Import ListNotations.

Theorem list_forallb_append : forall (p:nat->bool) l1 l2, forallb p (l1 ++ l2) = forallb p l1 && forallb p l2.
Proof. intros p l1 l2. induction l1 as [|x xs IH]; simpl. reflexivity. rewrite IH, andb_assoc. reflexivity. Qed.
