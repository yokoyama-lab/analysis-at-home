(* leaf: ceval_ass_inv | difficulty ★ | depends_on: [] *)
Lemma ceval_ass_inv : forall x a s s' k,
  ceval (CAss x a) s s' k ->
  s' = mk_state (arr s) (upd (vars s) x (aeval s a)) /\ k = 0.
Proof. intros. inversion H; subst. auto. Qed.
