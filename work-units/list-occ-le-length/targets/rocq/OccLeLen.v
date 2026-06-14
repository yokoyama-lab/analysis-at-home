(* analysis@home — work unit: list-occ-le-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The number of occurrences of x is at most the list length. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint occ (x:nat)(l:list nat) := match l with [] => 0 | y::ys => (if y =? x then 1 else 0) + occ x ys end.
Theorem list_occ_le_length : forall x l, occ x l <= length l.
Proof. intros x l. induction l as [|y ys IH]; simpl. lia. destruct (y =? x); lia. Qed.
