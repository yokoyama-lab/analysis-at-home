(* leaf: outer_body_effect | difficulty ★★★ | depends_on:
   [ceval_seq_inv, ceval_ass_inv, ceval_arrass_inv, inner_loop_bound,
    inner_loop_preserves, ceval_arr_length, list_set_length] *)
Lemma outer_body_effect : forall s s' k,
  ceval outer_body s s' k ->
  k <= vars s vi /\ vars s' vi = S (vars s vi) /\ length (arr s') = length (arr s).
Proof.
  intros s s' k H. unfold outer_body in H.
  apply ceval_seq_inv in H; destruct H as [s1 [ka [kb [HA [H1 Hk]]]]].
  apply ceval_ass_inv in HA; destruct HA as [Hs1 HkA].
  apply ceval_seq_inv in H1; destruct H1 as [s2 [kb1 [kb2 [HB [H2 Hk1]]]]].
  apply ceval_ass_inv in HB; destruct HB as [Hs2 HkB].
  apply ceval_seq_inv in H2; destruct H2 as [s3 [kc1 [kc2 [HW [H3 Hk2]]]]].
  apply ceval_seq_inv in H3; destruct H3 as [s4 [kd1 [kd2 [HC [HD Hk3]]]]].
  apply ceval_arrass_inv in HC; destruct HC as [Hs4 HkC].
  apply ceval_ass_inv in HD; destruct HD as [Hs' HkD].
  pose proof (inner_loop_bound _ _ _ HW) as Hib.
  pose proof (inner_loop_preserves _ _ _ HW) as Hip; destruct Hip as [Hpi _].
  pose proof (ceval_arr_length _ _ _ _ HW) as Hal.
  subst.
  unfold upd in *. simpl in *.
  repeat split.
  - lia.
  - rewrite Hpi. lia.
  - rewrite list_set_length. lia.
Qed.
