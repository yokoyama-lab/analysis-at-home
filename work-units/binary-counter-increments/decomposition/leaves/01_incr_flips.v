(* leaf: incr_flips | difficulty ★★ | depends_on: [] *)
Lemma incr_flips : forall bs,
  snd (incr bs) + count_ones (fst (incr bs)) = 2 + count_ones bs.
Proof.
  induction bs as [|b r IH].
  - reflexivity.
  - destruct b.
    + simpl. destruct (incr r) as [r' c] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. lia.
    + simpl. lia.
Qed.
