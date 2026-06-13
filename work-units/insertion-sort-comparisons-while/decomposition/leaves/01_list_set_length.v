(* leaf: list_set_length | difficulty ★ | depends_on: [] *)
Lemma list_set_length : forall l i v, length (list_set l i v) = length l.
Proof.
  induction l as [|h t IH]; intros i v.
  - destruct i; reflexivity.
  - destruct i; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
