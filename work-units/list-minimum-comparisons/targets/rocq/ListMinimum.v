(* analysis@home — work unit: list-minimum-comparisons (Rocq target)
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: closed-form.
 * VERIFIED (Print Assumptions: closed under the global context). Finding the
 * minimum of a length-n list uses exactly n-1 comparisons. lean/agda/isabelle open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint minc (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | x :: xs => match xs with
               | [] => (x, 0)
               | _ => let '(m, c) := minc xs in ((if x <=? m then x else m), S c)
               end
  end.

Theorem list_minimum_comparisons : forall l, snd (minc l) = length l - 1.
Proof.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct xs as [|y ys].
    + reflexivity.
    + destruct (minc (y :: ys)) as [m c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. simpl. lia.
Qed.
