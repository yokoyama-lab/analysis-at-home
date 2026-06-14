(* analysis@home — work unit: insertion-sort-preserves-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Insertion sort returns a list of the same length as its input. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint insert (x:nat) (l:list nat) : list nat :=
  match l with [] => [x] | y::ys => if x <=? y then x::y::ys else y :: insert x ys end.
Fixpoint isort (l:list nat) : list nat := match l with [] => [] | x::xs => insert x (isort xs) end.
Lemma insert_length : forall x l, length (insert x l) = S (length l).
Proof. intros x l. induction l as [|y ys IH]; simpl. reflexivity. destruct (x <=? y); simpl. reflexivity. rewrite IH. reflexivity. Qed.
Theorem isort_preserves_length : forall l, length (isort l) = length l.
Proof. induction l as [|x xs IH]; simpl. reflexivity. rewrite insert_length, IH. reflexivity. Qed.
