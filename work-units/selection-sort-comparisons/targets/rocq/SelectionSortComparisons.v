(* analysis@home — work unit: selection-sort-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: closed-form.
 *
 * VERIFIED (no Admitted/Axiom; Print Assumptions: closed under the global
 * context). Selection sort always performs EXACTLY n(n-1)/2 comparisons,
 * regardless of the data — an exact closed form, stated without division as
 * 2 * comparisons l = length l * (length l - 1).
 * The lean/agda/isabelle targets remain open. *)

Require Import List Arith Lia.
Import ListNotations.

(* select the minimum of (x :: l): returns (min, the remaining elements, #comparisons).
   Each recursion step performs exactly one comparison (y <? x). *)
Fixpoint select (x : nat) (l : list nat) : nat * list nat * nat :=
  match l with
  | [] => (x, [], 0)
  | y :: ys =>
      let '(m, rest, c) := select (if y <? x then y else x) ys in
      (m, (if y <? x then x else y) :: rest, S c)
  end.

(* selection sort with fuel (= length is enough); returns (sorted, #comparisons). *)
Fixpoint ssort (fuel : nat) (l : list nat) : list nat * nat :=
  match fuel with
  | 0 => ([], 0)
  | S f =>
      match l with
      | [] => ([], 0)
      | x :: xs =>
          let '(m, rest, c1) := select x xs in
          let '(sorted, c2) := ssort f rest in
          (m :: sorted, c1 + c2)
      end
  end.

Definition comparisons (l : list nat) : nat := snd (ssort (length l) l).

(* selecting the min of x::l uses exactly |l| comparisons *)
Lemma select_count : forall l x, snd (select x l) = length l.
Proof.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - simpl. destruct (select (if y <? x then y else x) ys) as [[m rest] c] eqn:E. simpl.
    specialize (IH (if y <? x then y else x)). rewrite E in IH. simpl in IH. lia.
Qed.

(* selecting the min preserves the number of remaining elements *)
Lemma select_len : forall l x, length (snd (fst (select x l))) = length l.
Proof.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - simpl. destruct (select (if y <? x then y else x) ys) as [[m rest] c] eqn:E. simpl.
    specialize (IH (if y <? x then y else x)). rewrite E in IH. simpl in IH. lia.
Qed.

Lemma ssort_cost : forall fuel l,
  length l <= fuel -> 2 * snd (ssort fuel l) = length l * (length l - 1).
Proof.
  induction fuel as [|f IH]; intros l Hlen.
  - assert (l = []) by (destruct l; simpl in Hlen; [reflexivity | lia]).
    subst. reflexivity.
  - destruct l as [|x xs].
    + reflexivity.
    + simpl. destruct (select x xs) as [[m rest] c1] eqn:Es.
      destruct (ssort f rest) as [sorted c2] eqn:Et. simpl.
      pose proof (select_count xs x) as Hc. rewrite Es in Hc. simpl in Hc.
      pose proof (select_len xs x) as Hl. rewrite Es in Hl. simpl in Hl.
      assert (Hrest : length rest <= f) by (simpl in Hlen; lia).
      specialize (IH rest Hrest). rewrite Et in IH. simpl in IH.
      rewrite Hl in IH.
      remember (length xs) as n.
      replace (S n - 1) with n by lia.
      rewrite Hc.
      destruct n as [|k].
      * simpl in IH. lia.
      * replace (S k - 1) with k in IH by lia. nia.
Qed.

(* Exact: selection sort on a list of length n always uses n(n-1)/2 comparisons. *)
Theorem selection_sort_comparisons_exact : forall l,
  2 * comparisons l = length l * (length l - 1).
Proof.
  intros l. unfold comparisons. apply ssort_cost. lia.
Qed.
