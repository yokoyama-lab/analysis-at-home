(* leaf: incr_n_invariant | difficulty ★★ | depends_on: [incr_flips] *)
Lemma incr_n_invariant : forall n,
  snd (incr_n n) + count_ones (fst (incr_n n)) = 2 * n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl. destruct (incr_n k) as [bs tot] eqn:E.
    destruct (incr bs) as [bs' c] eqn:E2. simpl.
    pose proof (incr_flips bs) as Hf. rewrite E2 in Hf. simpl in Hf.
    simpl in IH. lia.
Qed.
