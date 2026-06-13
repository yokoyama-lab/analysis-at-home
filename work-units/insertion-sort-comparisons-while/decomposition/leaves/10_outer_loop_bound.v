(* leaf: outer_loop_bound | difficulty ★★★★ | depends_on: [outer_body_effect]
   The arithmetic core. The two `assert`s (HBC, HBA) are themselves natural
   sub-leaves if this one proves too hard for a contributor to one-shot. *)
Lemma outer_loop_bound : forall s s' k,
  ceval (CWhile outer_guard outer_body) s s' k ->
  2 * k <= length (arr s) * (length (arr s) - 1)
           - vars s vi * (vars s vi - 1).
Proof.
  intros s s' k H.
  remember (CWhile outer_guard outer_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - inversion Hw; subst b c; clear Hw.
    unfold outer_guard in H; simpl in H; injection H as Hval Hcost; subst kb.
    lia.
  - inversion Hw; subst b c.
    pose proof (outer_body_effect _ _ _ H0) as [Hk1 [Hvi Hlen]].
    unfold outer_guard in H; simpl in H; injection H as Hval Hcost; subst kb.
    apply Nat.leb_le in Hval.
    specialize (IHceval2 eq_refl).
    rewrite Hvi, Hlen in IHceval2.
    replace (S (vars s vi) - 1) with (vars s vi) in IHceval2 by lia.
    remember (length (arr s)) as n.
    remember (vars s vi) as i.
    assert (HBC : S i * i = i * (i - 1) + 2 * i).
    { destruct i; simpl; [reflexivity | nia]. }
    assert (HBA : S i * i <= n * (n - 1)).
    { destruct n as [|n']; [lia | ].
      replace (S n' - 1) with n' by lia.
      assert (i <= n') by lia. nia. }
    remember (n * (n - 1)) as A.
    remember (S i * i) as B.
    remember (i * (i - 1)) as C.
    clear HeqA HeqB HeqC Heqn Heqi.
    lia.
Qed.
