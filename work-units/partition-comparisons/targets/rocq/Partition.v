(* analysis@home — work unit: partition-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Partitioning n elements around a pivot uses n comparisons. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint partitionc (piv : nat) (l : list nat) : (list nat * list nat) * nat :=
  match l with
  | [] => (([], []), 0)
  | x :: xs => let '((lo, hi), c) := partitionc piv xs in
               ((if x <? piv then (x :: lo, hi) else (lo, x :: hi)), S c)
  end.
Theorem partition_comparisons : forall piv l, snd (partitionc piv l) = length l.
Proof. intros piv l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (partitionc piv xs) as [[lo hi] c] eqn:E. cbn [snd].
    try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
