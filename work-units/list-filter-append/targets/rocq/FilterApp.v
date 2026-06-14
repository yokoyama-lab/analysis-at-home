(* analysis@home — work unit: list-filter-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). filter p (l1 ++ l2) = filter p l1 ++ filter p l2. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_filter_append : forall (p:nat->bool) l1 l2, filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof. intros p l1 l2. induction l1 as [|x xs IH]; simpl. reflexivity. destruct (p x); simpl; rewrite IH; reflexivity. Qed.
