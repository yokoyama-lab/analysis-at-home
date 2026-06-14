(* analysis@home — work unit: sorted-zero-inversions (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A sorted list has zero inversions. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint gtc (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | y :: ys => (if y <? x then 1 else 0) + gtc x ys end.
Fixpoint inv (l : list nat) : nat :=
  match l with [] => 0 | x :: xs => gtc x xs + inv xs end.
Fixpoint sorted (l : list nat) : Prop :=
  match l with [] => True | x :: xs => (forall y, In y xs -> x <= y) /\ sorted xs end.
Lemma gtc_zero : forall x l, (forall y, In y l -> x <= y) -> gtc x l = 0.
Proof.
  intros x l. induction l as [|y ys IH]; intro Hh.
  - reflexivity.
  - simpl. assert (x <= y) by (apply Hh; left; reflexivity).
    assert ((y <? x) = false) by (apply Nat.ltb_ge; lia). rewrite H0.
    simpl. apply IH. intros z Hz. apply Hh. right. exact Hz.
Qed.
Theorem sorted_zero_inversions : forall l, sorted l -> inv l = 0.
Proof.
  induction l as [|x xs IH]; intro Hs.
  - reflexivity.
  - simpl. destruct Hs as [Hle Hs']. rewrite (gtc_zero x xs Hle). rewrite (IH Hs'). reflexivity.
Qed.
