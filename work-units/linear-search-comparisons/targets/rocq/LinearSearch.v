(* analysis@home — work unit: linear-search-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: complexity.
 *
 * VERIFIED (Print Assumptions: closed under the global context). Linear search
 * over a list of length n uses at most n key comparisons. The lean/agda/isabelle
 * targets, and a found-iff-In correctness companion, are open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint lsearch (x : nat) (l : list nat) : bool * nat :=
  match l with
  | [] => (false, 0)
  | y :: ys => if x =? y then (true, 1) else let '(b, c) := lsearch x ys in (b, S c)
  end.

Theorem linear_search_comparisons : forall x l, snd (lsearch x l) <= length l.
Proof.
  intros x l. induction l as [|y ys IH].
  - simpl. lia.
  - simpl. destruct (x =? y).
    + simpl. lia.
    + destruct (lsearch x ys) as [b c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
Qed.
