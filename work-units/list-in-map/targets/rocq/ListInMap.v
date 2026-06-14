(* analysis@home — work unit: list-in-map (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). If x is in l then f x is in map f l. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_In_map : forall (f:nat->nat) x l, In x l -> In (f x) (map f l).
Proof. intros f x l H. induction l as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct H as [->|H]. left; reflexivity. right; apply IH; exact H. Qed.
