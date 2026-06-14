(* assembly: the O(n log n) bound from the leaves (split/merge are Opaque from
   the msort_length leaf onward, so `simpl` only steps the outer msort). *)
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
