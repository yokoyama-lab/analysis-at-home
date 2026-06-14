(* analysis@home — work unit: merge-sort-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: complexity.
 *
 * VERIFIED (no Admitted/Axiom; Print Assumptions: closed under the global
 * context). Merge sort is O(n log n): with a level budget k such that
 * length l <= 2^k, it performs at most k * length l comparisons. Taking the
 * least such k = ceil(log2 n) gives the n*ceil(log2 n) bound.
 * The lean/agda/isabelle targets remain open. *)

Require Import List Arith Lia.
Import ListNotations.

(* balanced split (alternating): |fst| = ceil(n/2), |snd| = floor(n/2) *)
Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest => let (a, b) := split rest in (x :: a, y :: b)
  end.

(* merge with fuel; counts one comparison per merge step *)
Fixpoint merge (fuel : nat) (l1 l2 : list nat) : list nat * nat :=
  match fuel with
  | 0 => (l1 ++ l2, 0)
  | S f =>
      match l1, l2 with
      | [], _ => (l2, 0)
      | _, [] => (l1, 0)
      | x :: xs, y :: ys =>
          if x <=? y then let (m, c) := merge f xs l2 in (x :: m, S c)
          else            let (m, c) := merge f l1 ys in (y :: m, S c)
      end
  end.

(* merge sort with a level budget k; valid when length l <= 2^k *)
Fixpoint msort (k : nat) (l : list nat) : list nat * nat :=
  match k with
  | 0 => (l, 0)
  | S k' =>
      match l with
      | [] => ([], 0)
      | [x] => ([x], 0)
      | _ =>
          let (l1, l2) := split l in
          let (s1, c1) := msort k' l1 in
          let (s2, c2) := msort k' l2 in
          let (m, cm) := merge (length s1 + length s2) s1 s2 in
          (m, c1 + c2 + cm)
      end
  end.

Definition comparisons (k : nat) (l : list nat) : nat := snd (msort k l).

(* ---- split ---- *)
Lemma split_total : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  fix IH 1. intros [|x [|y rest]]; simpl; try reflexivity.
  destruct (split rest) as [a b] eqn:E. simpl.
  specialize (IH rest). rewrite E in IH. simpl in IH. lia.
Qed.

Lemma split_balance : forall l,
  2 * length (fst (split l)) <= S (length l) /\
  2 * length (snd (split l)) <= length l.
Proof.
  fix IH 1. intros [|x [|y rest]]; simpl; try (split; lia).
  destruct (split rest) as [a b] eqn:E. simpl.
  specialize (IH rest). rewrite E in IH. simpl in IH. lia.
Qed.

(* ---- merge ---- *)
Lemma merge_length : forall fuel l1 l2,
  length (fst (merge fuel l1 l2)) = length l1 + length l2.
Proof.
  induction fuel as [|f IH]; intros l1 l2.
  - simpl. rewrite length_app. reflexivity.
  - destruct l1 as [|x xs]; [reflexivity|].
    destruct l2 as [|y ys]; [simpl; lia|].
    simpl. destruct (x <=? y).
    + destruct (merge f xs (y :: ys)) as [m c] eqn:E. simpl.
      specialize (IH xs (y :: ys)). rewrite E in IH. simpl in IH. simpl. lia.
    + destruct (merge f (x :: xs) ys) as [m c] eqn:E. simpl.
      specialize (IH (x :: xs) ys). rewrite E in IH. simpl in IH. simpl. lia.
Qed.

Lemma merge_cost : forall fuel l1 l2,
  snd (merge fuel l1 l2) <= length l1 + length l2.
Proof.
  induction fuel as [|f IH]; intros l1 l2.
  - simpl. lia.
  - destruct l1 as [|x xs]; [simpl; lia|].
    destruct l2 as [|y ys]; [simpl; lia|].
    simpl. destruct (x <=? y).
    + destruct (merge f xs (y :: ys)) as [m c] eqn:E. simpl.
      specialize (IH xs (y :: ys)). rewrite E in IH. simpl in IH. simpl. lia.
    + destruct (merge f (x :: xs) ys) as [m c] eqn:E. simpl.
      specialize (IH (x :: xs) ys). rewrite E in IH. simpl in IH. simpl. lia.
Qed.

(* keep split/merge folded so `simpl` only unfolds the outer msort step *)
Opaque split merge.

(* ---- msort ---- *)
Lemma msort_length : forall k l, length (fst (msort k l)) = length l.
Proof.
  induction k as [|k' IH]; intros l.
  - reflexivity.
  - destruct l as [|x [|y rest]]; [reflexivity|reflexivity|].
    simpl. destruct (split (x :: y :: rest)) as [l1 l2] eqn:Es.
    destruct (msort k' l1) as [s1 c1] eqn:E1.
    destruct (msort k' l2) as [s2 c2] eqn:E2.
    destruct (merge (length s1 + length s2) s1 s2) as [m cm] eqn:Em. simpl.
    pose proof (merge_length (length s1 + length s2) s1 s2) as Hm. rewrite Em in Hm. simpl in Hm.
    pose proof (IH l1) as H1. rewrite E1 in H1. simpl in H1.
    pose proof (IH l2) as H2. rewrite E2 in H2. simpl in H2.
    pose proof (split_total (x :: y :: rest)) as Ht. rewrite Es in Ht. simpl in Ht.
    lia.
Qed.

(* O(n log n): at most k * length l comparisons when length l <= 2^k. *)
Theorem merge_sort_comparisons_nlogn : forall k l,
  length l <= 2 ^ k -> comparisons k l <= k * length l.
Proof.
  unfold comparisons. induction k as [|k' IH]; intros l Hk.
  - simpl. lia.
  - destruct l as [|x [|y rest]].
    + simpl. lia.
    + simpl. lia.
    + rewrite Nat.pow_succ_r' in Hk. simpl in Hk.
      simpl (msort _ _).
      destruct (split (x :: y :: rest)) as [l1 l2] eqn:Es.
      destruct (msort k' l1) as [s1 c1] eqn:E1.
      destruct (msort k' l2) as [s2 c2] eqn:E2.
      destruct (merge (length s1 + length s2) s1 s2) as [m cm] eqn:Em. simpl.
      pose proof (split_total (x :: y :: rest)) as Ht. rewrite Es in Ht. simpl in Ht.
      pose proof (split_balance (x :: y :: rest)) as Hb. rewrite Es in Hb. simpl in Hb. destruct Hb as [Hb1 Hb2].
      pose proof (msort_length k' l1) as Hl1. rewrite E1 in Hl1. simpl in Hl1.
      pose proof (msort_length k' l2) as Hl2. rewrite E2 in Hl2. simpl in Hl2.
      pose proof (merge_cost (length s1 + length s2) s1 s2) as Hcm. rewrite Em in Hcm. simpl in Hcm.
      rewrite Hl1, Hl2 in Hcm.
      assert (Hk1 : length l1 <= 2 ^ k') by lia.
      assert (Hk2 : length l2 <= 2 ^ k') by lia.
      pose proof (IH l1 Hk1) as Ic1. rewrite E1 in Ic1. simpl in Ic1.
      pose proof (IH l2 Hk2) as Ic2. rewrite E2 in Ic2. simpl in Ic2.
      simpl (length (x :: y :: rest)).
      rewrite <- Ht.
      nia.
Qed.
