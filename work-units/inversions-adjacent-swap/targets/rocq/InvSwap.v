(* analysis@home — work unit: inversions-adjacent-swap (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). One adjacent out-of-order swap removes exactly one inversion. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint gtc (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | y :: ys => (if y <? x then 1 else 0) + gtc x ys end.
Fixpoint inv (l : list nat) : nat :=
  match l with [] => 0 | x :: xs => gtc x xs + inv xs end.
Theorem inversions_adjacent_swap :
  forall a b l, b < a -> inv (a :: b :: l) = S (inv (b :: a :: l)).
Proof.
  intros a b l Hba. simpl.
  assert (Ht : (b <? a) = true) by (apply Nat.ltb_lt; lia).
  assert (Hf : (a <? b) = false) by (apply Nat.ltb_ge; lia).
  rewrite Ht, Hf. simpl. lia.
Qed.
