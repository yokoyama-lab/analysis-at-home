(* leaf: inner_body_effect | difficulty ★★ | depends_on: [ceval_seq_inv, ceval_arrass_inv, ceval_ass_inv] *)
Lemma inner_body_effect : forall s s1 k1,
  ceval inner_body s s1 k1 ->
  k1 = 0 /\ vars s1 vj = vars s vj - 1 /\ vars s1 vi = vars s vi /\ vars s1 vkey = vars s vkey.
Proof.
  intros s s1 k1 H. unfold inner_body in H.
  apply ceval_seq_inv in H. destruct H as [sm [km1 [km2 [Ha [Hb Hk]]]]].
  apply ceval_arrass_inv in Ha. destruct Ha as [Hsm Hk1].
  apply ceval_ass_inv in Hb. destruct Hb as [Hs1 Hk2].
  subst. unfold upd. simpl. repeat split; reflexivity.
Qed.
