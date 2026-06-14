(* leaf: ssort_cost | difficulty ★★★ | depends_on: [select_count, select_len] *)
Lemma ssort_cost : forall fuel l,
  length l <= fuel -> 2 * snd (ssort fuel l) = length l * (length l - 1).
Proof.
  induction fuel as [|f IH]; intros l Hlen.
  - assert (l = []) by (destruct l; simpl in Hlen; [reflexivity | lia]).
    subst. reflexivity.
  - destruct l as [|x xs].
    + reflexivity.
    + simpl. destruct (select x xs) as [[m rest] c1] eqn:Es.
      destruct (ssort f rest) as [sorted c2] eqn:Et. simpl.
      pose proof (select_count xs x) as Hc. rewrite Es in Hc. simpl in Hc.
      pose proof (select_len xs x) as Hl. rewrite Es in Hl. simpl in Hl.
      assert (Hrest : length rest <= f) by (simpl in Hlen; lia).
      specialize (IH rest Hrest). rewrite Et in IH. simpl in IH.
      rewrite Hl in IH.
      remember (length xs) as n.
      replace (S n - 1) with n by lia.
      rewrite Hc.
      destruct n as [|k].
      * simpl in IH. lia.
      * replace (S k - 1) with k in IH by lia. nia.
Qed.
