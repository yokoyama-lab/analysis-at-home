(* leaf: merge_length | difficulty ★★ | depends_on: [] *)
Lemma merge_length : forall fuel l1 l2,
  length (fst (merge fuel l1 l2)) = length l1 + length l2.
Proof.
  induction fuel as [|f IH]; intros l1 l2.
  - simpl. rewrite length_app. reflexivity.
  - destruct l1 as [|x xs]; [reflexivity|].
    destruct l2 as [|y ys]; [simpl; lia|].
    simpl. destruct (x <=? y).
    + destruct (merge f xs (y :: ys)) as [m c] eqn:E. simpl.
      specialize (IH xs (y :: ys)). rewrite E in IH. simpl in IH. simpl. lia.
    + destruct (merge f (x :: xs) ys) as [m c] eqn:E. simpl.
      specialize (IH (x :: xs) ys). rewrite E in IH. simpl in IH. simpl. lia.
Qed.
