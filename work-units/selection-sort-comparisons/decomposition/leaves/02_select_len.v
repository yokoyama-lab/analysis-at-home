(* leaf: select_len | difficulty ★★ | depends_on: [] *)
Lemma select_len : forall l x, length (snd (fst (select x l))) = length l.
Proof.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - simpl. destruct (select (if y <? x then y else x) ys) as [[m rest] c] eqn:E. simpl.
    specialize (IH (if y <? x then y else x)). rewrite E in IH. simpl in IH. lia.
Qed.
