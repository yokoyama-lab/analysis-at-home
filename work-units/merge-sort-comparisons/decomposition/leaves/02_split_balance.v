(* leaf: split_balance | difficulty ★★ | depends_on: [] *)
Lemma split_balance : forall l,
  2 * length (fst (split l)) <= S (length l) /\
  2 * length (snd (split l)) <= length l.
Proof.
  fix IH 1. intros [|x [|y rest]]; simpl; try (split; lia).
  destruct (split rest) as [a b] eqn:E. simpl.
  specialize (IH rest). rewrite E in IH. simpl in IH. lia.
Qed.
