(* analysis@home — work unit: list-maximum-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: closed-form.
 *
 * VERIFIED (Print Assumptions: closed under the global context). Finding the
 * maximum of a list of length n uses exactly n-1 comparisons. The
 * lean/agda/isabelle targets are open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint maxc (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | x :: xs =>
      match xs with
      | [] => (x, 0)
      | _ => let '(m, c) := maxc xs in ((if x <=? m then m else x), S c)
      end
  end.

Theorem list_maximum_comparisons : forall l, snd (maxc l) = length l - 1.
Proof.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct xs as [|y ys].
    + reflexivity.
    + destruct (maxc (y :: ys)) as [m c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. simpl. lia.
Qed.
