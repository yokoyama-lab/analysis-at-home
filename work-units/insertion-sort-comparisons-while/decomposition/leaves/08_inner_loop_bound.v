(* leaf: inner_loop_bound | difficulty ★★★ | depends_on: [inner_body_effect] *)
Lemma inner_loop_bound : forall s s' k,
  ceval (CWhile inner_guard inner_body) s s' k -> k <= vars s vj.
Proof.
  intros s s' k H.
  remember (CWhile inner_guard inner_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - inversion Hw; subst b c; clear Hw.
    unfold inner_guard in H. simpl in H.
    remember (vars s vj) as jv eqn:Hjv.
    destruct jv as [|m]; simpl in H; inversion H; lia.
  - inversion Hw; subst b c.
    specialize (IHceval2 eq_refl).
    apply inner_body_effect in H0. destruct H0 as [Hk1 [Hvj _]].
    unfold inner_guard in H. simpl in H.
    remember (vars s vj) as jv eqn:Hjv.
    destruct jv as [|m]; simpl in H.
    + inversion H.
    + inversion H. rewrite Hvj in IHceval2. simpl in IHceval2. lia.
Qed.
