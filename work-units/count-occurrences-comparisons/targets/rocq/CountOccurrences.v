(* analysis@home — work unit: count-occurrences-comparisons (Rocq target)
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: closed-form.
 * VERIFIED (Print Assumptions: closed under the global context). Counting how
 * many times x occurs in a length-n list uses exactly n comparisons. lean/agda/isabelle open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint countc (x : nat) (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | y :: ys => let '(n, c) := countc x ys in ((if x =? y then S n else n), S c)
  end.

Theorem count_occurrences_comparisons : forall x l, snd (countc x l) = length l.
Proof.
  intros x. induction l as [|y ys IH].
  - reflexivity.
  - simpl. destruct (countc x ys) as [n c] eqn:E. simpl.
    try (rewrite E in IH). simpl in IH. lia.
Qed.
