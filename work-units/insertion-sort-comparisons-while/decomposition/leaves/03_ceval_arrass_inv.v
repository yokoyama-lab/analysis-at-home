(* leaf: ceval_arrass_inv | difficulty ★ | depends_on: [] *)
Lemma ceval_arrass_inv : forall i a s s' k,
  ceval (CArrAss i a) s s' k ->
  s' = mk_state (list_set (arr s) (aeval s i) (aeval s a)) (vars s) /\ k = 0.
Proof. intros. inversion H; subst. auto. Qed.
