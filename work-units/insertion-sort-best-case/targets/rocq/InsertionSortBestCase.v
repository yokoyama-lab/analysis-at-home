(* analysis@home — work unit: insertion-sort-best-case (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: best-case.
 *
 * The best case of insertion sort: a list of length n needs at least n-1 key
 * comparisons (one to place each element after the first into a non-empty sorted
 * prefix). The bound is achieved by an already-sorted input. Stated as
 *   length l <= S (comparisons l)
 * to stay in nat (i.e. comparisons l >= length l - 1).
 *
 * Together with insertion-sort-comparisons (worst case: 2*c <= n*(n-1)) this
 * brackets insertion sort between a linear best case and a quadratic worst case.
 *
 * The insert/isort cost model is identical to insertion-sort-comparisons.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

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

(* insert into a non-empty list costs at least one comparison. *)
Lemma insert_comparisons_lower :
  forall x l, 1 <= length l -> 1 <= snd (insert x l).
Proof.
  intros x l H. destruct l as [|y ys].
  - simpl in H. lia.
  - simpl. destruct (x <=? y).
    + simpl. lia.
    + destruct (insert x ys) as [l' c]. simpl. lia.
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

Theorem insertion_sort_best_case :
  forall l, length l <= S (comparisons l).
Proof.
  intros l. unfold comparisons. induction l as [|x xs IH].
  - simpl. lia.
  - simpl. destruct (isort xs) as [xs' c1] eqn:E1.
    pose proof (isort_length xs) as HL. try (rewrite E1 in HL). simpl in HL.
    try (rewrite E1 in IH). simpl in IH.
    destruct (insert x xs') as [l' c2] eqn:E2. simpl.
    destruct xs' as [|z zs].
    + (* xs' = [] : length xs = 0, so the bound is trivial *)
      simpl in HL. lia.
    + (* xs' non-empty : the insert costs at least one comparison *)
      assert (Hnz : 1 <= length (z :: zs)) by (simpl; lia).
      pose proof (insert_comparisons_lower x (z :: zs) Hnz) as HC.
      try (rewrite E2 in HC). simpl in HC.
      simpl in HL. lia.
Qed.
