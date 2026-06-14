(* leaf: split_total | difficulty ★★ | depends_on: [] *)
Lemma split_total : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  fix IH 1. intros [|x [|y rest]]; simpl; try reflexivity.
  destruct (split rest) as [a b] eqn:E. simpl.
  specialize (IH rest). rewrite E in IH. simpl in IH. lia.
Qed.
