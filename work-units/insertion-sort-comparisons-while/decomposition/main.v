(* assembly: proves the theorem from the leaf lemmas (no new induction). *)
Theorem insertion_sort_while_comparisons_upper_bound :
  forall (l : list nat) (s' : state) (k : nat),
    ceval insertion_sort (init l) s' k ->
    2 * k <= length l * (length l - 1).
Proof.
  intros l s' k H. unfold insertion_sort in H.
  apply ceval_seq_inv in H. destruct H as [s1 [k1 [k2 [HI [HW Hk]]]]].
  apply ceval_ass_inv in HI. destruct HI as [Hs1 HkI]. subst k1 k.
  pose proof (outer_loop_bound _ _ _ HW) as Hob.
  assert (Hvi1 : vars s1 vi = 1) by (rewrite Hs1; unfold init, upd; simpl; reflexivity).
  assert (Hlen1 : length (arr s1) = length l) by (rewrite Hs1; unfold init; simpl; reflexivity).
  rewrite Hvi1, Hlen1 in Hob.
  replace (1 * (1 - 1)) with 0 in Hob by lia.
  rewrite Nat.sub_0_r in Hob.
  lia.
Qed.
