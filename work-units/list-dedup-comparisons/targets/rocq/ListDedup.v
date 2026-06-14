(* analysis@home — work unit: list-dedup-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Removing adjacent duplicates uses n-1 comparisons. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint dedupc (l : list nat) : nat :=
  match l with
  | [] => 0
  | [_] => 0
  | x :: (y :: _) as r => S (dedupc r)
  end.
Theorem list_dedup_comparisons : forall l, dedupc l = pred (length l).
Proof. induction l as [|x xs IH].
  - reflexivity.
  - destruct xs as [|y ys].
    + reflexivity.
    + simpl in *. lia. Qed.
