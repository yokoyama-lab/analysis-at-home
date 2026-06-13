(* leaf: ceval_seq_inv | difficulty ★ | depends_on: [] *)
Lemma ceval_seq_inv : forall c1 c2 s s' k,
  ceval (CSeq c1 c2) s s' k ->
  exists s1 k1 k2, ceval c1 s s1 k1 /\ ceval c2 s1 s' k2 /\ k = k1 + k2.
Proof. intros. inversion H; subst. exists s1, k1, k2. auto. Qed.
