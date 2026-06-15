(* analysis@home — work unit: binary-search-correct (Rocq target).
 *
 * Binary search over a sorted (monotone non-decreasing) array `a` on the index
 * window [lo, hi) is correct: it reports the key present iff some index in the
 * window holds it. Soundness needs nothing; completeness uses monotonicity to
 * argue the key, if present, stays in the half the search recurses into.
 *   bsearch_correct : monotone a -> hi - lo <= fuel ->
 *     (bsearch fuel a key lo hi = true <-> exists i, lo <= i < hi /\ a i = key).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint bsearch (fuel : nat) (a : nat -> nat) (key lo hi : nat) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      if hi <=? lo then false
      else if a (lo + (hi - lo) / 2) =? key then true
      else if a (lo + (hi - lo) / 2) <? key
           then bsearch f a key (S (lo + (hi - lo) / 2)) hi
           else bsearch f a key lo (lo + (hi - lo) / 2)
  end.

(* Soundness: a "true" verdict always exhibits a matching index in the window. *)
Lemma bsearch_sound : forall fuel a key lo hi,
  bsearch fuel a key lo hi = true -> exists i, lo <= i < hi /\ a i = key.
Proof.
  induction fuel as [|f IH]; intros a key lo hi H; cbn [bsearch] in H; [discriminate|].
  destruct (hi <=? lo) eqn:Ehl; [discriminate|]. apply Nat.leb_gt in Ehl.
  set (mid := lo + (hi - lo) / 2) in *.
  assert (Hd : (hi - lo) / 2 < hi - lo) by (apply Nat.div_lt; lia).
  assert (Hm : lo <= mid < hi) by (unfold mid; lia).
  destruct (a mid =? key) eqn:Em.
  - apply Nat.eqb_eq in Em. exists mid. split; [lia | exact Em].
  - destruct (a mid <? key) eqn:El.
    + apply IH in H as [i [Hi Hai]]. exists i. split; [lia | exact Hai].
    + apply IH in H as [i [Hi Hai]]. exists i. split; [lia | exact Hai].
Qed.

(* Completeness: if the key is in the window, the search finds it. *)
Lemma bsearch_complete : forall fuel a key lo hi,
  (forall i j, i <= j -> a i <= a j) -> hi - lo <= fuel ->
  (exists i, lo <= i < hi /\ a i = key) -> bsearch fuel a key lo hi = true.
Proof.
  induction fuel as [|f IH]; intros a key lo hi Hmono Hf [i [[Hlo Hhi] Hai]].
  - lia.
  - cbn [bsearch]. destruct (hi <=? lo) eqn:Ehl.
    + apply Nat.leb_le in Ehl. lia.
    + apply Nat.leb_gt in Ehl.
      set (mid := lo + (hi - lo) / 2) in *.
      assert (Hd : (hi - lo) / 2 < hi - lo) by (apply Nat.div_lt; lia).
      destruct (a mid =? key) eqn:Em; [reflexivity|].
      apply Nat.eqb_neq in Em.
      destruct (a mid <? key) eqn:El.
      * apply Nat.ltb_lt in El.
        apply IH; [exact Hmono | unfold mid; lia |].
        assert (mid < i).
        { destruct (le_lt_dec i mid) as [Hle|?]; [pose proof (Hmono i mid Hle); lia | lia]. }
        exists i. split; [lia | exact Hai].
      * apply Nat.ltb_ge in El.
        apply IH; [exact Hmono | unfold mid; lia |].
        assert (i < mid).
        { destruct (le_lt_dec mid i) as [Hle|?]; [pose proof (Hmono mid i Hle); lia | lia]. }
        exists i. split; [lia | exact Hai].
Qed.

Theorem bsearch_correct : forall fuel a key lo hi,
  (forall i j, i <= j -> a i <= a j) -> hi - lo <= fuel ->
  (bsearch fuel a key lo hi = true <-> exists i, lo <= i < hi /\ a i = key).
Proof.
  intros fuel a key lo hi Hmono Hf. split.
  - apply bsearch_sound.
  - apply bsearch_complete; assumption.
Qed.
