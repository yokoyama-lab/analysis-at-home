(* analysis@home — work unit: ordered-insertion-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: complexity.
 *
 * VERIFIED (Print Assumptions: closed under the global context). Inserting one
 * element into a length-n list (the inner step of insertion sort) uses at most
 * n comparisons. The lean/agda/isabelle targets are open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint insert (x : nat) (l : list nat) : list nat * nat :=
  match l with
  | [] => ([x], 0)
  | y :: ys => if x <=? y then (x :: y :: ys, 1) else let '(l', c) := insert x ys in (y :: l', S c)
  end.

Theorem ordered_insertion_comparisons : forall x l, snd (insert x l) <= length l.
Proof.
  intros x l. induction l as [|y ys IH].
  - simpl. lia.
  - simpl. destruct (x <=? y).
    + simpl. lia.
    + destruct (insert x ys) as [l' c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
Qed.
