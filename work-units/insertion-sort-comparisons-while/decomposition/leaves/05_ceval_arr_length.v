(* leaf: ceval_arr_length | difficulty ★★ | depends_on: [list_set_length] *)
Lemma ceval_arr_length : forall c s s' k,
  ceval c s s' k -> length (arr s') = length (arr s).
Proof.
  intros c s s' k H. induction H; simpl in *;
    try (rewrite list_set_length); lia.
Qed.
