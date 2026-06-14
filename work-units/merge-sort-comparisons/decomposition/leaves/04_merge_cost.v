(* leaf: merge_cost | difficulty ★★ | depends_on: [] *)
Lemma merge_cost : forall fuel l1 l2,
  snd (merge fuel l1 l2) <= length l1 + length l2.
Proof.
  induction fuel as [|f IH]; intros l1 l2.
  - simpl. lia.
  - destruct l1 as [|x xs]; [simpl; lia|].
    destruct l2 as [|y ys]; [simpl; lia|].
    simpl. destruct (x <=? y).
    + destruct (merge f xs (y :: ys)) as [m c] eqn:E. simpl.
      specialize (IH xs (y :: ys)). rewrite E in IH. simpl in IH. simpl. lia.
    + destruct (merge f (x :: xs) ys) as [m c] eqn:E. simpl.
      specialize (IH (x :: xs) ys). rewrite E in IH. simpl in IH. simpl. lia.
Qed.
