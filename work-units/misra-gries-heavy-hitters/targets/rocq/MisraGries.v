(* analysis@home — work unit: misra-gries-heavy-hitters (Rocq target).
 *
 * The Misra-Gries summary (1982) generalizes Boyer-Moore: with only k-1 counters
 * it finds every "heavy hitter" — every element occurring MORE than n/k times —
 * in one pass over a stream of length n. (k = 2 is Boyer-Moore majority.)
 * Counters form a dictionary of (item,count); on each stream element a:
 *   - if a is stored, increment its count;
 *   - else if fewer than k-1 items are stored, store (a,1);
 *   - else decrement every stored count by 1 (dropping any that reach 0).
 * The generalized cancellation invariant, with D = number of decrement steps:
 *   cnt x stream <= getc x dict + D     and     total dict + k*D = length stream.
 * Hence k*D <= n, so any x with k*(cnt x) > n keeps a positive counter:
 *   misra_gries : 2 <= k -> length l < k * cnt m l -> 0 < getc m (mg k l).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List.
Import ListNotations.

Fixpoint cnt (a : nat) (l : list nat) : nat :=
  match l with [] => 0 | y :: ys => (if a =? y then 1 else 0) + cnt a ys end.

Definition dict := list (nat * nat).
Fixpoint getc (a : nat) (d : dict) : nat :=
  match d with [] => 0 | (b,c) :: t => (if a =? b then c else 0) + getc a t end.
Fixpoint total (d : dict) : nat :=
  match d with [] => 0 | (_,c) :: t => c + total t end.
Fixpoint incr (a : nat) (d : dict) : dict :=
  match d with
  | [] => [(a,1)]
  | (b,c) :: t => if a =? b then (b, S c) :: t else (b,c) :: incr a t
  end.
Definition decr_all (d : dict) : dict :=
  filter (fun p => 0 <? snd p) (map (fun p => (fst p, pred (snd p))) d).
Definition ALLPOS (d : dict) : Prop := Forall (fun p => 1 <= snd p) d.

(* ---- key sets of incr ---- *)
Lemma keys_incr_in : forall a d, In a (map fst d) -> map fst (incr a d) = map fst d.
Proof.
  induction d as [|[b c] t IH]; cbn [incr map fst]; intro H; [now elim H|].
  destruct (a =? b) eqn:E; cbn [map fst]; [reflexivity|].
  f_equal. apply IH. destruct H as [H|H]; [subst; now rewrite Nat.eqb_refl in E | exact H].
Qed.

Lemma keys_incr_notin : forall a d, ~ In a (map fst d) -> map fst (incr a d) = map fst d ++ [a].
Proof.
  induction d as [|[b c] t IH]; cbn [incr map fst app]; intro H; [reflexivity|].
  destruct (a =? b) eqn:E.
  - apply Nat.eqb_eq in E; subst. exfalso; apply H; now left.
  - cbn [map fst app]. f_equal. apply IH. intro; apply H; now right.
Qed.

Lemma getc_incr_same : forall a d, getc a (incr a d) = S (getc a d).
Proof.
  induction d as [|[b c] t IH]; cbn [incr getc].
  - now rewrite Nat.eqb_refl.
  - destruct (a =? b) eqn:E; cbn [getc]; rewrite ?E; lia.
Qed.

Lemma getc_incr_other : forall a b d, a <> b -> getc b (incr a d) = getc b d.
Proof.
  intros a b d Hab. induction d as [|[e c] t IH]; cbn [incr getc].
  - destruct (b =? a) eqn:E; [apply Nat.eqb_eq in E; lia | lia].
  - destruct (a =? e) eqn:E; cbn [getc]; rewrite ?IH; try lia.
    apply Nat.eqb_eq in E; subst e.
    destruct (b =? a) eqn:E2; [apply Nat.eqb_eq in E2; lia | lia].
Qed.

Lemma total_incr : forall a d, total (incr a d) = S (total d).
Proof.
  induction d as [|[b c] t IH]; cbn [incr total].
  - reflexivity.
  - destruct (a =? b) eqn:E; cbn [total]; lia.
Qed.

Lemma allpos_incr : forall a d, ALLPOS d -> ALLPOS (incr a d).
Proof.
  unfold ALLPOS. induction d as [|[b c] t IH]; cbn [incr]; intro H.
  - constructor; [cbn [snd]; lia | constructor].
  - inversion H as [|? ? Hc Ht]; subst. cbn [snd] in Hc.
    destruct (a =? b).
    + constructor; [cbn [snd]; lia | exact Ht].
    + constructor; [cbn [snd]; exact Hc | apply IH; exact Ht].
Qed.

Lemma size_incr_in : forall a d, In a (map fst d) -> length (incr a d) = length d.
Proof.
  intros a d H.
  rewrite <- (map_length fst (incr a d)), (keys_incr_in a d H), map_length. reflexivity.
Qed.

Lemma size_incr_notin : forall a d, ~ In a (map fst d) -> length (incr a d) = S (length d).
Proof.
  intros a d H.
  rewrite <- (map_length fst (incr a d)), (keys_incr_notin a d H), app_length, map_length.
  cbn [length]. lia.
Qed.

Lemma getc_pos_in : forall a d, 0 < getc a d -> In a (map fst d).
Proof.
  induction d as [|[b c] t IH]; cbn [getc map fst]; intro H; [lia|].
  destruct (a =? b) eqn:E.
  - apply Nat.eqb_eq in E; subst; now left.
  - right. apply IH. lia.
Qed.

Lemma notin_getc0 : forall a d, ~ In a (map fst d) -> getc a d = 0.
Proof.
  induction d as [|[b c] t IH]; cbn [getc map fst]; intro H; [reflexivity|].
  destruct (a =? b) eqn:E.
  - apply Nat.eqb_eq in E; subst. exfalso; apply H; now left.
  - rewrite IH; [reflexivity|]. intro; apply H; now right.
Qed.

Lemma allpos_total_ge_size : forall d, ALLPOS d -> length d <= total d.
Proof.
  induction d as [|[b c] t IH]; cbn [length total]; intro H; [lia|].
  inversion H as [|? ? Hc Ht]; subst. cbn [snd] in Hc. specialize (IH Ht). lia.
Qed.

Lemma total_filter_pos : forall m, total (filter (fun p => 0 <? snd p) m) = total m.
Proof.
  induction m as [|[b c] t IH]; [reflexivity|].
  cbn [filter total snd]. destruct (0 <? c) eqn:E; cbn [total].
  - lia.
  - apply Nat.ltb_ge in E. lia.
Qed.

Lemma total_map_pred : forall d,
  ALLPOS d -> total (map (fun p => (fst p, pred (snd p))) d) = total d - length d.
Proof.
  induction d as [|[b c] t IH]; cbn [map total length]; intro H; [reflexivity|].
  inversion H as [|? ? Hc Ht]; subst. cbn [fst snd pred] in *.
  pose proof (allpos_total_ge_size t Ht). rewrite (IH Ht). lia.
Qed.

Lemma total_decr : forall d, ALLPOS d -> total (decr_all d) = total d - length d.
Proof.
  intros d H. unfold decr_all. rewrite total_filter_pos. now apply total_map_pred.
Qed.

Lemma size_decr_le : forall d, length (decr_all d) <= length d.
Proof.
  intro d. unfold decr_all.
  apply Nat.le_trans with (m := length (map (fun p => (fst p, pred (snd p))) d)).
  - apply filter_length_le.
  - rewrite map_length. apply le_n.
Qed.

Lemma allpos_decr : forall d, ALLPOS (decr_all d).
Proof.
  intro d. unfold decr_all, ALLPOS. apply Forall_forall. intros p Hp.
  apply filter_In in Hp as [_ Hpos]. destruct (snd p); [discriminate|]. cbn; lia.
Qed.

Lemma keys_decr_incl : forall d, incl (map fst (decr_all d)) (map fst d).
Proof.
  intros d x Hx. unfold decr_all in Hx.
  apply in_map_iff in Hx as [p [Hpx Hp]].
  apply filter_In in Hp as [Hp _].
  apply in_map_iff in Hp as [q [Hq Hqd]].
  apply in_map_iff. exists q. subst p. cbn [fst] in Hpx. split; [exact Hpx | exact Hqd].
Qed.

Lemma keys_filter_incl : forall (f : nat * nat -> bool) (l : dict),
  incl (map fst (filter f l)) (map fst l).
Proof.
  intros f l x Hx. apply in_map_iff in Hx as [p [Hp Hin]].
  apply filter_In in Hin as [Hin _].
  apply in_map_iff. exists p. split; [exact Hp | exact Hin].
Qed.

Lemma nodup_map_fst_filter : forall (f : nat * nat -> bool) (l : dict),
  NoDup (map fst l) -> NoDup (map fst (filter f l)).
Proof.
  induction l as [|[b c] t IH]; intro H; [now cbn|].
  cbn [map fst] in H. inversion H as [|? ? Hb Ht]; subst.
  cbn [filter]. destruct (f (b,c)); cbn [map fst].
  - constructor.
    + intro Hin. apply Hb. apply (keys_filter_incl f t). exact Hin.
    + apply IH; exact Ht.
  - apply IH; exact Ht.
Qed.

Lemma keys_map_pred : forall d : dict,
  map fst (map (fun p => (fst p, pred (snd p))) d) = map fst d.
Proof.
  induction d as [|[b c] t IH]; cbn [map fst]; [reflexivity | now f_equal].
Qed.

Lemma nodup_decr : forall d, NoDup (map fst d) -> NoDup (map fst (decr_all d)).
Proof.
  intros d H. unfold decr_all. apply nodup_map_fst_filter.
  rewrite keys_map_pred. exact H.
Qed.

Lemma getc_cons_eq : forall b v t, getc b ((b,v) :: t) = v + getc b t.
Proof. intros b v t. cbn [getc]. now rewrite Nat.eqb_refl. Qed.

Lemma getc_cons_neq : forall x b v t, x <> b -> getc x ((b,v) :: t) = getc x t.
Proof.
  intros x b v t H. cbn [getc].
  destruct (x =? b) eqn:E; [apply Nat.eqb_eq in E; contradiction | lia].
Qed.

Lemma decr_all_cons : forall b c t,
  decr_all ((b,c)::t) = if 0 <? pred c then (b, pred c) :: decr_all t else decr_all t.
Proof.
  intros b c t. unfold decr_all. cbn [map filter fst snd].
  destruct (0 <? pred c); reflexivity.
Qed.

Lemma getc_decr_le : forall x d,
  NoDup (map fst d) -> ALLPOS d -> getc x d <= S (getc x (decr_all d)).
Proof.
  induction d as [|[b c] t IH]; intros Hnd Hap; [cbn [getc]; lia|].
  cbn [map fst] in Hnd. inversion Hnd as [|? ? Hb Ht]; subst.
  inversion Hap as [|? ? Hc Hap']; subst. cbn [snd] in Hc.
  specialize (IH Ht Hap').
  assert (Hbd : ~ In b (map fst (decr_all t)))
    by (intro Hin; apply Hb; apply (keys_decr_incl t); exact Hin).
  destruct c as [|c0]; [lia|]. rewrite decr_all_cons. cbn [pred].
  destruct (Nat.eq_dec x b) as [->|Hxb].
  - rewrite (getc_cons_eq b (S c0) t), (notin_getc0 b t Hb).
    destruct (0 <? c0) eqn:Ec.
    + rewrite (getc_cons_eq b c0 (decr_all t)), (notin_getc0 b (decr_all t) Hbd). lia.
    + apply Nat.ltb_ge in Ec. rewrite (notin_getc0 b (decr_all t) Hbd). lia.
  - rewrite (getc_cons_neq x b (S c0) t Hxb).
    destruct (0 <? c0) eqn:Ec.
    + rewrite (getc_cons_neq x b c0 (decr_all t) Hxb). exact IH.
    + exact IH.
Qed.

(* ---- count over the stream ---- *)
Lemma cnt_app : forall x l m, cnt x (l ++ m) = cnt x l + cnt x m.
Proof. intros x l m; induction l as [|y ys IH]; cbn [cnt app]; [reflexivity| rewrite IH; lia]. Qed.
Lemma cnt_snoc_eq : forall a l, cnt a (l ++ [a]) = S (cnt a l).
Proof. intros a l. rewrite cnt_app. cbn [cnt]. rewrite Nat.eqb_refl. lia. Qed.
Lemma cnt_snoc_neq : forall x a l, x <> a -> cnt x (l ++ [a]) = cnt x l.
Proof.
  intros x a l H. rewrite cnt_app. cbn [cnt].
  destruct (x =? a) eqn:E; [apply Nat.eqb_eq in E; contradiction | lia].
Qed.

Lemma in_getc_pos : forall a d, ALLPOS d -> In a (map fst d) -> 0 < getc a d.
Proof.
  induction d as [|[b c] t IH]; intros Hap Hin; [now elim Hin|].
  inversion Hap as [|? ? Hc Hap']; subst. cbn [snd] in Hc.
  cbn [map fst] in Hin. cbn [getc]. destruct (a =? b) eqn:E; [lia|].
  destruct Hin as [Hin|Hin]; [subst b; now rewrite Nat.eqb_refl in E | specialize (IH Hap' Hin); lia].
Qed.

Lemma nodup_snoc : forall (l : list nat) a, NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
  induction l as [|y ys IH]; intros a H Hni; cbn [app].
  - constructor; [intro Hf; inversion Hf | constructor].
  - inversion H as [|? ? Hy Hys]; subst. constructor.
    + rewrite in_app_iff. intros [Hin | Hin].
      * apply Hy; exact Hin.
      * cbn in Hin. destruct Hin as [He | Hf]; [subst; apply Hni; now left | destruct Hf].
    + apply IH; [exact Hys | intro; apply Hni; now right].
Qed.

(* ---- the one-pass Misra-Gries summary ---- *)
Definition step (k : nat) (s : dict * nat) (a : nat) : dict * nat :=
  let (d, D) := s in
  if 0 <? getc a d then (incr a d, D)
  else if length d <? (k - 1) then (incr a d, D)
  else (decr_all d, S D).

Definition mg (k : nat) (l : list nat) : dict :=
  fst (fold_left (step k) l ([], 0)).

Definition INV (k : nat) (l : list nat) (s : dict * nat) : Prop :=
  let (d, D) := s in
  NoDup (map fst d) /\ ALLPOS d /\ length d <= k - 1 /\
  total d + k * D = length l /\
  (forall x, cnt x l <= getc x d + D).

Lemma mg_inv : forall k l, 2 <= k -> INV k l (fold_left (step k) l ([], 0)).
Proof.
  intros k l Hk. unfold INV. induction l as [|a l IHl] using rev_ind.
  - cbn. repeat split; [constructor | constructor | lia | lia | intros x; cbn [cnt getc]; lia].
  - rewrite fold_left_app. cbn [fold_left].
    destruct (fold_left (step k) l ([], 0)) as [d D].
    destruct IHl as (Hnd & Hap & Hsz & Htot & Hcnt).
    rewrite app_length; cbn [length].
    unfold step. destruct (0 <? getc a d) eqn:Epos.
    + apply Nat.ltb_lt in Epos.
      assert (Hin : In a (map fst d)) by (apply getc_pos_in; lia).
      repeat split.
      * rewrite keys_incr_in by exact Hin. exact Hnd.
      * apply allpos_incr; exact Hap.
      * rewrite size_incr_in by exact Hin. exact Hsz.
      * rewrite total_incr. lia.
      * intro x. destruct (Nat.eq_dec x a) as [->|Hxa].
        -- rewrite cnt_snoc_eq, getc_incr_same. specialize (Hcnt a). lia.
        -- rewrite (cnt_snoc_neq x a l Hxa), (getc_incr_other a x d (not_eq_sym Hxa)).
           specialize (Hcnt x). lia.
    + apply Nat.ltb_ge in Epos. assert (Hg0 : getc a d = 0) by lia.
      assert (Hnin : ~ In a (map fst d)) by
        (intro Hin; pose proof (in_getc_pos a d Hap Hin); lia).
      destruct (length d <? (k - 1)) eqn:Eroom.
      * apply Nat.ltb_lt in Eroom. repeat split.
        -- rewrite keys_incr_notin by exact Hnin. apply nodup_snoc; [exact Hnd | exact Hnin].
        -- apply allpos_incr; exact Hap.
        -- rewrite size_incr_notin by exact Hnin. lia.
        -- rewrite total_incr. lia.
        -- intro x. destruct (Nat.eq_dec x a) as [->|Hxa].
           ++ rewrite cnt_snoc_eq, getc_incr_same. specialize (Hcnt a). lia.
           ++ rewrite (cnt_snoc_neq x a l Hxa), (getc_incr_other a x d (not_eq_sym Hxa)).
              specialize (Hcnt x). lia.
      * apply Nat.ltb_ge in Eroom. assert (Hfull : length d = k - 1) by lia.
        repeat split.
        -- apply nodup_decr; exact Hnd.
        -- apply allpos_decr.
        -- pose proof (size_decr_le d). lia.
        -- pose proof (total_decr d Hap). pose proof (allpos_total_ge_size d Hap). lia.
        -- intro x. destruct (Nat.eq_dec x a) as [->|Hxa].
           ++ rewrite cnt_snoc_eq. specialize (Hcnt a). rewrite Hg0 in Hcnt. lia.
           ++ rewrite (cnt_snoc_neq x a l Hxa).
              specialize (Hcnt x). pose proof (getc_decr_le x d Hnd Hap). lia.
Qed.

(* Misra-Gries guarantee: every element occurring more than n/k times keeps a
   positive counter — found with only k-1 counters. (k = 2 is Boyer-Moore.) *)
Theorem misra_gries : forall k l m,
  2 <= k -> length l < k * cnt m l -> 0 < getc m (mg k l).
Proof.
  intros k l m Hk Hmaj. unfold mg.
  pose proof (mg_inv k l Hk) as H. unfold INV in H.
  destruct (fold_left (step k) l ([], 0)) as [d D].
  destruct H as (_ & _ & _ & Htot & Hcnt). cbn [fst].
  specialize (Hcnt m). nia.
Qed.
