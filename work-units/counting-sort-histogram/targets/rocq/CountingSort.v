(* analysis@home — work unit: counting-sort-histogram (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Counting sort's buckets partition the input: the histogram sums to the length. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint cnt (v:nat)(l:list nat) := match l with [] => 0 | x::xs => (if x =? v then 1 else 0) + cnt v xs end.
Fixpoint sumhist (K:nat)(l:list nat) := match K with 0 => 0 | S k => sumhist k l + cnt k l end.

Lemma sumhist_nil : forall K, sumhist K [] = 0.
Proof. induction K as [|k IH]; simpl. reflexivity. rewrite IH. reflexivity. Qed.

Lemma ind_lt_succ : forall x k,
  (if x <? k then 1 else 0) + (if x =? k then 1 else 0) = (if x <? S k then 1 else 0).
Proof. intros x k. destruct (Nat.ltb_spec x k); destruct (Nat.eqb_spec x k);
  destruct (Nat.ltb_spec x (S k)); lia. Qed.

Lemma sumhist_cons : forall K x xs, sumhist K (x :: xs) = sumhist K xs + (if x <? K then 1 else 0).
Proof. induction K as [|k IH]; intros x xs; simpl.
  - lia.
  - rewrite IH. pose proof (ind_lt_succ x k). lia. Qed.

(* Counting sort places each key in its own bucket: the buckets partition the
   input, so the histogram sums to the input length. A comparison-free, linear
   invariant — the basis of distribution counting / radix sort. *)
Theorem counting_sort_histogram :
  forall l K, (forall x, In x l -> x < K) -> sumhist K l = length l.
Proof.
  induction l as [|x xs IH]; intros K Hall.
  - apply sumhist_nil.
  - rewrite sumhist_cons.
    assert (Hlt : x < K) by (apply Hall; left; reflexivity).
    destruct (x <? K) eqn:E.
    + simpl. assert (sumhist K xs = length xs) by
        (apply IH; intros y Hy; apply Hall; right; exact Hy). lia.
    + apply Nat.ltb_ge in E. lia.
Qed.
