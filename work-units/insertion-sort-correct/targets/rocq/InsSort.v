(* analysis@home — work unit: insertion-sort-correct (Rocq target).
 *
 * Insertion sort is CORRECT: its output is sorted and is a permutation of the
 * input (so no element is lost, duplicated, or invented). This is the
 * correctness companion to `insertion-sort-comparisons` (the n(n-1)/2 cost).
 *   isort_correct : Sorted (isort l) /\ Permutation (isort l) l.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List Permutation.
Import ListNotations.

Inductive Sorted : list nat -> Prop :=
  | srt_nil  : Sorted []
  | srt_one  : forall x, Sorted [x]
  | srt_cons : forall x y l, x <= y -> Sorted (y :: l) -> Sorted (x :: y :: l).

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: t => if x <=? y then x :: y :: t else y :: insert x t
  end.
Fixpoint isort (l : list nat) : list nat :=
  match l with [] => [] | x :: t => insert x (isort t) end.

Lemma insert_sorted : forall x l, Sorted l -> Sorted (insert x l).
Proof.
  intros x l H. induction H as [|y|a b l Hab Hs IH]; cbn [insert].
  - apply srt_one.
  - destruct (x <=? y) eqn:E.
    + apply Nat.leb_le in E. apply srt_cons; [exact E | apply srt_one].
    + apply Nat.leb_gt in E. apply srt_cons; [lia | apply srt_one].
  - destruct (x <=? a) eqn:Ea.
    + apply Nat.leb_le in Ea. apply srt_cons; [exact Ea | apply srt_cons; assumption].
    + apply Nat.leb_gt in Ea. cbn [insert] in IH. destruct (x <=? b) eqn:Eb.
      * apply Nat.leb_le in Eb. apply srt_cons; [lia | exact IH].
      * apply srt_cons; [exact Hab | exact IH].
Qed.

Lemma insert_perm : forall x l, Permutation (insert x l) (x :: l).
Proof.
  intros x l. induction l as [|y t IH]; cbn [insert].
  - apply Permutation_refl.
  - destruct (x <=? y) eqn:E.
    + apply Permutation_refl.
    + apply (Permutation_trans (l' := y :: x :: t)).
      * apply perm_skip, IH.
      * apply perm_swap.
Qed.

Theorem isort_correct : forall l, Sorted (isort l) /\ Permutation (isort l) l.
Proof.
  induction l as [|x t [Hs Hp]]; cbn [isort].
  - split; [apply srt_nil | apply Permutation_refl].
  - split.
    + apply insert_sorted, Hs.
    + apply (Permutation_trans (insert_perm x (isort t))). apply perm_skip, Hp.
Qed.
