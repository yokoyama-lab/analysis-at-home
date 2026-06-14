(* analysis@home — work unit: merge-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Merging two lists uses at most length(l1)+length(l2) key comparisons. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint mergec (fuel : nat) (l1 l2 : list nat) : nat :=
  match fuel with 0 => 0
  | S f => match l1, l2 with
           | [], _ => 0 | _, [] => 0
           | x::xs, y::ys => S (if x <=? y then mergec f xs l2 else mergec f l1 ys)
           end end.
Theorem merge_comparisons : forall fuel l1 l2, mergec fuel l1 l2 <= length l1 + length l2.
Proof. induction fuel as [|f IH]; intros l1 l2; simpl. lia.
  destruct l1 as [|x xs]. lia. destruct l2 as [|y ys]. lia.
  destruct (x <=? y).
  - specialize (IH xs (y::ys)). simpl in *. lia.
  - specialize (IH (x::xs) ys). simpl in *. lia. Qed.
