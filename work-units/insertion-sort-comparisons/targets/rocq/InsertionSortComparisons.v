(* analysis@home — work unit: insertion-sort-comparisons (Rocq target)
 *
 * VERIFIED. The cost model (insert / isort / comparisons) is fixed; the
 * worst-case comparison bound below is proved (no Admitted/Axiom — checked with
 * `Print Assumptions`: closed under the global context). CI compiles this file
 * with coqc. This Rocq target is done; the lean/agda/isabelle targets remain
 * open work units. *)

Require Import List Arith Lia.
Import ListNotations.

(* Instrumented insertion: returns the updated list together with the number
   of key comparisons performed (each [x <=? y] test counts as one). *)
Fixpoint insert (x : nat) (l : list nat) : list nat * nat :=
  match l with
  | [] => ([x], 0)
  | y :: ys =>
      if x <=? y then (x :: y :: ys, 1)
      else let (l', c) := insert x ys in (y :: l', S c)
  end.

Fixpoint isort (l : list nat) : list nat * nat :=
  match l with
  | [] => ([], 0)
  | x :: xs =>
      let (xs', c1) := isort xs in
      let (l', c2) := insert x xs' in
      (l', c1 + c2)
  end.

Definition comparisons (l : list nat) : nat := snd (isort l).

(* insert performs at most [length l] comparisons. *)
Lemma insert_comparisons : forall x l, snd (insert x l) <= length l.
Proof.
  intros x l. induction l as [|y ys IH].
  - simpl. lia.
  - simpl. destruct (x <=? y).
    + simpl. lia.
    + destruct (insert x ys) as [l' c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
Qed.

(* insert grows the list by exactly one element. *)
Lemma insert_length : forall x l, length (fst (insert x l)) = S (length l).
Proof.
  intros x l. induction l as [|y ys IH].
  - reflexivity.
  - simpl. destruct (x <=? y).
    + reflexivity.
    + destruct (insert x ys) as [l' c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
Qed.

(* isort preserves length. *)
Lemma isort_length : forall l, length (fst (isort l)) = length l.
Proof.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. destruct (isort xs) as [xs' c1] eqn:E1.
    destruct (insert x xs') as [l' c2] eqn:E2. simpl.
    try (rewrite E1 in IH). simpl in IH.
    pose proof (insert_length x xs') as IL. try (rewrite E2 in IL). simpl in IL.
    lia.
Qed.

(* Worst case: insertion sort uses at most n*(n-1)/2 key comparisons,
   stated without division.

   Proof idea: inserting the i-th element costs at most i comparisons
   (insert_comparisons + length preservation), and the i range over a list of
   length n sums to n*(n-1)/2. The induction step: with m = length xs,
     2*(c1+c2) = 2*c1 + 2*c2 <= m*(m-1) + 2*m = m*(m+1) = (m+1)*m,
   which is exactly (S m)*((S m) - 1). *)
Theorem insertion_sort_comparisons_upper_bound :
  forall l : list nat,
    2 * comparisons l <= length l * (length l - 1).
Proof.
  intros l. unfold comparisons. induction l as [|x xs IH].
  - simpl. lia.
  - simpl. destruct (isort xs) as [xs' c1] eqn:E1.
    destruct (insert x xs') as [l' c2] eqn:E2. simpl.
    try (rewrite E1 in IH). simpl in IH.
    pose proof (insert_comparisons x xs') as HC. try (rewrite E2 in HC). simpl in HC.
    pose proof (isort_length xs) as HL. try (rewrite E1 in HL). simpl in HL.
    rewrite HL in HC.
    remember (length xs) as m eqn:Em. clear Em E1 E2 HL.
    destruct m as [|k].
    + simpl in *. lia.
    + simpl in IH. simpl. nia.
Qed.
