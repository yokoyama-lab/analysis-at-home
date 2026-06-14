(* leaf: msort_length | difficulty ★★★ | depends_on: [split_total, merge_length]
   Needs split/merge folded so `simpl` only unfolds the outer msort step; the
   Opaque command below scopes from here on (after the split/merge leaves). *)
Opaque split merge.
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
