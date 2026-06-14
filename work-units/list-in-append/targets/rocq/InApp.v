(* analysis@home — work unit: list-in-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). In x (l1 ++ l2) iff In x l1 or In x l2. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_In_app : forall (x:nat) l1 l2, In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof. intros x l1 l2. induction l1 as [|y ys IH]; simpl; [tauto | rewrite IH; tauto]. Qed.
