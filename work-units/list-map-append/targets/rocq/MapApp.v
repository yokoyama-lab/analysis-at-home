(* analysis@home — work unit: list-map-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). map f (l1 ++ l2) = map f l1 ++ map f l2. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_map_append : forall (f:nat->nat) l1 l2, map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof. intros f l1 l2. induction l1 as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
