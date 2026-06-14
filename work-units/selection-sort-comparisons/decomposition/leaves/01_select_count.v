(* leaf: select_count | difficulty ★★ | depends_on: [] *)
Lemma select_count : forall l x, snd (select x l) = length l.
Proof.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - simpl. destruct (select (if y <? x then y else x) ys) as [[m rest] c] eqn:E. simpl.
    specialize (IH (if y <? x then y else x)). rewrite E in IH. simpl in IH. lia.
Qed.
