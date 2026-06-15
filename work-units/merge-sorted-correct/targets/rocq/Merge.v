(* analysis@home — work unit: merge-sorted-correct (Rocq target).
 *
 * Merging two SORTED lists yields a sorted list that is a permutation of their
 * concatenation — the heart of merge sort. `merge` is fuel-bounded (the total
 * length strictly decreases). Correctness:
 *   merge_correct : Sorted l1 -> Sorted l2 -> length l1 + length l2 <= fuel ->
 *     Sorted (merge fuel l1 l2) /\ Permutation (merge fuel l1 l2) (l1 ++ l2).
 * The sortedness proof carries a lower-bound (`le_hd`) through the recursion so
 * the emitted head stays >= everything before it.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List Permutation.
Import ListNotations.

Inductive Sorted : list nat -> Prop :=
  | srt_nil  : Sorted []
  | srt_one  : forall x, Sorted [x]
  | srt_cons : forall x y l, x <= y -> Sorted (y :: l) -> Sorted (x :: y :: l).

Definition le_hd (z : nat) (l : list nat) : Prop :=
  match l with [] => True | x :: _ => z <= x end.

Lemma sorted_tl : forall x l, Sorted (x :: l) -> Sorted l.
Proof. intros x l H; inversion H; subst; [apply srt_nil | assumption]. Qed.
Lemma sorted_le_hd : forall x l, Sorted (x :: l) -> le_hd x l.
Proof. intros x l H; inversion H; subst; [exact I | assumption]. Qed.
Lemma cons_sorted : forall x l, Sorted l -> le_hd x l -> Sorted (x :: l).
Proof.
  intros x [|y l0] Hs Hh; [apply srt_one | apply srt_cons; [exact Hh | exact Hs]].
Qed.

Fixpoint merge (fuel : nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | 0 => l1 ++ l2
  | S f =>
      match l1 with
      | [] => l2
      | x :: t1 =>
          match l2 with
          | [] => l1
          | y :: t2 => if x <=? y then x :: merge f t1 l2 else y :: merge f l1 t2
          end
      end
  end.

Lemma merge_perm : forall fuel l1 l2,
  length l1 + length l2 <= fuel -> Permutation (merge fuel l1 l2) (l1 ++ l2).
Proof.
  induction fuel as [|f IH]; intros l1 l2 Hf; cbn [merge].
  - apply Permutation_refl.
  - destruct l1 as [|x t1]; [apply Permutation_refl|].
    destruct l2 as [|y t2]; [rewrite app_nil_r; apply Permutation_refl|].
    cbn [length] in Hf. destruct (x <=? y) eqn:E.
    + cbn [app]. apply perm_skip. apply IH. cbn [length]. lia.
    + apply (Permutation_trans (l' := y :: (x :: t1) ++ t2)).
      * apply perm_skip. apply IH. cbn [length]. lia.
      * apply Permutation_middle.
Qed.

Lemma merge_sorted_aux : forall fuel l1 l2,
  length l1 + length l2 <= fuel -> Sorted l1 -> Sorted l2 ->
  Sorted (merge fuel l1 l2) /\
  (forall z, le_hd z l1 -> le_hd z l2 -> le_hd z (merge fuel l1 l2)).
Proof.
  induction fuel as [|f IH]; intros l1 l2 Hf Hs1 Hs2; cbn [merge].
  - destruct l1 as [|x t1]; destruct l2 as [|y t2]; cbn [length] in Hf;
      try (exfalso; lia).
    cbn [app]. split; [apply srt_nil | intros; exact I].
  - destruct l1 as [|x t1]; [split; [exact Hs2 | intros z _ Hz2; exact Hz2]|].
    destruct l2 as [|y t2]; [split; [exact Hs1 | intros z Hz1 _; exact Hz1]|].
    cbn [length] in Hf. destruct (x <=? y) eqn:E.
    + apply Nat.leb_le in E.
      destruct (IH t1 (y :: t2)) as [HM Hhd];
        [cbn [length]; lia | apply (sorted_tl x); exact Hs1 | exact Hs2 |].
      split.
      * apply cons_sorted; [exact HM | apply Hhd; [apply (sorted_le_hd x); exact Hs1 | exact E]].
      * intros z Hz1 _. exact Hz1.
    + apply Nat.leb_gt in E.
      destruct (IH (x :: t1) t2) as [HM Hhd];
        [cbn [length]; lia | exact Hs1 | apply (sorted_tl y); exact Hs2 |].
      split.
      * apply cons_sorted; [exact HM | apply Hhd; [cbn [le_hd]; lia | apply (sorted_le_hd y); exact Hs2]].
      * intros z _ Hz2. exact Hz2.
Qed.

Theorem merge_correct : forall fuel l1 l2,
  Sorted l1 -> Sorted l2 -> length l1 + length l2 <= fuel ->
  Sorted (merge fuel l1 l2) /\ Permutation (merge fuel l1 l2) (l1 ++ l2).
Proof.
  intros fuel l1 l2 Hs1 Hs2 Hf. split.
  - apply (merge_sorted_aux fuel l1 l2 Hf Hs1 Hs2).
  - apply merge_perm, Hf.
Qed.
