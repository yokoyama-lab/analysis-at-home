(* analysis@home — work unit: list-indexof-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Finding the index of x uses at most n comparisons. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint indexofc (x : nat) (l : list nat) : option nat * nat :=
  match l with
  | [] => (None, 0)
  | y :: ys => if x =? y then (Some 0, 1) else let '(r, c) := indexofc x ys in (r, S c)
  end.
Theorem list_indexof_comparisons : forall x l, snd (indexofc x l) <= length l.
Proof. intros x l. induction l as [|y ys IH].
  - simpl. lia.
  - simpl. destruct (x =? y).
    + cbn [snd]. lia.
    + destruct (indexofc x ys) as [r c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
