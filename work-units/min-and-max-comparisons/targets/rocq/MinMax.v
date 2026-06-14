(* analysis@home — work unit: min-and-max-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Naive min-and-max scan uses 2 comparisons per element. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint mmc (mn mx : nat) (l : list nat) : (nat * nat) * nat :=
  match l with
  | [] => ((mn, mx), 0)
  | x :: xs => let mn' := if x <? mn then x else mn in
               let mx' := if mx <? x then x else mx in
               let '((a, b), c) := mmc mn' mx' xs in ((a, b), S (S c))
  end.
Theorem minmax_comparisons : forall l mn mx, snd (mmc mn mx l) = 2 * length l.
Proof. induction l as [|x xs IH]; intros mn mx.
  - reflexivity.
  - simpl. destruct (mmc (if x <? mn then x else mn) (if mx <? x then x else mx) xs) as [[a b] c] eqn:E.
    cbn [snd]. specialize (IH (if x <? mn then x else mn) (if mx <? x then x else mx)).
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
