(* leaf: inner_loop_preserves | difficulty ★★ | depends_on: [inner_body_effect] *)
Lemma inner_loop_preserves : forall s s' k,
  ceval (CWhile inner_guard inner_body) s s' k ->
  vars s' vi = vars s vi /\ vars s' vkey = vars s vkey.
Proof.
  intros s s' k H. remember (CWhile inner_guard inner_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - inversion Hw; subst; split; reflexivity.
  - inversion Hw; subst b c. specialize (IHceval2 eq_refl).
    apply inner_body_effect in H0. destruct H0 as [_ [_ [Hvi Hvkey]]].
    destruct IHceval2 as [Hi Hk]. split.
    + rewrite Hi. exact Hvi.
    + rewrite Hk. exact Hvkey.
Qed.
