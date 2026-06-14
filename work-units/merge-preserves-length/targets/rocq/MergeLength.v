(* analysis@home — work unit: merge-preserves-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Merging two lists yields a list whose length is the sum of the inputs' lengths. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint mergel (fuel:nat) (l1 l2:list nat) : list nat :=
  match fuel with 0 => l1 ++ l2
  | S f => match l1, l2 with
           | [], _ => l2 | _, [] => l1
           | x::xs, y::ys => if x <=? y then x :: mergel f xs l2 else y :: mergel f l1 ys
           end end.
Theorem merge_preserves_length : forall fuel l1 l2, length l1 + length l2 <= fuel -> length (mergel fuel l1 l2) = length l1 + length l2.
Proof. induction fuel as [|f IH]; intros l1 l2 H; simpl.
  - rewrite app_length. reflexivity.
  - destruct l1 as [|x xs]. reflexivity. destruct l2 as [|y ys]. simpl; lia.
    destruct (x <=? y); simpl.
    + rewrite IH by (simpl in *; lia). simpl. lia.
    + rewrite IH by (simpl in *; lia). simpl. lia. Qed.
