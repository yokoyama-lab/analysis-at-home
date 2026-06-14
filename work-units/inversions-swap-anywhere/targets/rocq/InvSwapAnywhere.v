(* analysis@home — work unit: inversions-swap-anywhere (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A swap of an adjacent inverted pair anywhere in the list removes exactly one inversion. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint gtc (x:nat)(l:list nat) := match l with [] => 0 | y::ys => (if y <? x then 1 else 0) + gtc x ys end.
Fixpoint inv (l:list nat) := match l with [] => 0 | x::xs => gtc x xs + inv xs end.
Lemma gtc_app : forall x l1 l2, gtc x (l1 ++ l2) = gtc x l1 + gtc x l2.
Proof. intros x l1 l2. induction l1 as [|y ys IH]; simpl. reflexivity. rewrite IH. lia. Qed.
Theorem inversions_swap_anywhere :
  forall pre a b post, b < a -> inv (pre ++ a :: b :: post) = S (inv (pre ++ b :: a :: post)).
Proof.
  intros pre a b post Hba. induction pre as [|c cs IH]; simpl.
  - assert (Ht : (b <? a) = true) by (apply Nat.ltb_lt; lia).
    assert (Hf : (a <? b) = false) by (apply Nat.ltb_ge; lia).
    rewrite Ht, Hf. simpl. lia.
  - rewrite !gtc_app. rewrite IH.
    assert (gtc c (a :: b :: post) = gtc c (b :: a :: post)) by (simpl; lia).
    lia.
Qed.
