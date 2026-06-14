(* analysis@home — work unit: list-filter-in-weaken (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Any element of filter p l is an element of l. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_filter_In_weaken : forall (p:nat->bool) x l, In x (filter p l) -> In x l.
Proof. intros p x l. induction l as [|y ys IH]; simpl.
  - tauto.
  - destruct (p y); simpl; intro H.
    + destruct H as [H|H]. left; exact H. right; apply IH; exact H.
    + right; apply IH; exact H. Qed.
