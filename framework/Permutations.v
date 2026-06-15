(* analysis@home framework: permutation enumeration + average-case counting (axiom-free).
 *
 * Self-contained (stdlib only); CI compiles each framework file in isolation, so
 * everything the counting theorem needs lives here.
 *
 * PART 1 -- the generator `perms` lists every permutation of its input exactly once:
 *   perms_correct : In p (perms L) <-> Permutation L p
 *   length_perms  : length (perms L) = fact (length L)
 *   NoDup_perms   : NoDup L -> NoDup (perms L)
 * (with the inserts/Add correspondence inserts_Add and deletion inverse del_Add).
 *
 * PART 2 -- counting permutations by their first SELECTED element. For a boolean
 * subset S, count_first S v L counts permutations of L whose first S-element is v.
 * The key fact ("the first element of a subset of a uniform permutation is uniform")
 * is proved as an explicit transposition bijection (perms_relabel via swp):
 *   count_first_value : NoDup L -> S v = true -> In v L ->
 *                       length (filter S L) * count_first S v L = fact (length L).
 *
 * PART 3 -- the quicksort capstone (Stage 2 Part B). With S = betw a b (the closed
 * value-interval [a,b]) and comparedb the head-pivot quicksort "directly compared"
 * relation, a value-pair at interval distance d = b-a+1 is compared in exactly
 * 2*n!/d of the n! permutations -- division-free:
 *   compared_count : a < b -> b < n -> (b - a + 1) * num_compared a b n = 2 * fact n.
 * This is the combinatorial step a measure-theoretic development gets "for free";
 * here it is proved over the explicit permutation model. Combined with the
 * program-level pair decomposition cmp_eq_pairsum and the Part-A arithmetic
 * (QuicksortPairSum.v) it completes program -> closed form 2(n+1)H_n-4n end to end.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia Permutation.
Import ListNotations.

Fixpoint inserts (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: t => (x :: y :: t) :: map (fun z => y :: z) (inserts x t)
  end.
Fixpoint perms (l : list nat) : list (list nat) :=
  match l with [] => [[]] | x :: t => flat_map (inserts x) (perms t) end.

(* In q (inserts x s)  <->  q is s with x inserted somewhere (stdlib `Add`) *)
Lemma inserts_Add : forall x s q, In q (inserts x s) <-> Add x s q.
Proof.
  intros x s; induction s as [|y t IH]; intro q; cbn [inserts].
  - split.
    + intros [<-|[]]. constructor.
    + intro HA. inversion HA; subst. left; reflexivity.
  - split.
    + intros [<-|Hin]; [constructor|].
      apply in_map_iff in Hin as [q' [<- Hq']]. constructor. apply IH; exact Hq'.
    + intro HA. inversion HA; subst; [left; reflexivity| right].
      apply in_map_iff. eexists. split; [reflexivity| apply IH; eassumption].
Qed.

(* perms enumerates exactly the permutations of L *)
Lemma perms_correct : forall L p, In p (perms L) <-> Permutation L p.
Proof.
  induction L as [|x t IH]; intro p; cbn [perms].
  - split.
    + intros [<-|[]]. apply perm_nil.
    + intro HP. apply Permutation_nil in HP. subst. left; reflexivity.
  - rewrite in_flat_map. split.
    + intros [s [Hs Hq]]. apply IH in Hs. apply inserts_Add in Hq.
      apply Permutation_Add in Hq. apply (perm_trans (l':= x :: s)).
      * apply perm_skip; exact Hs.
      * exact Hq.
    + intro HP.
      assert (Hin : In x p) by (apply (Permutation_in _ HP); left; reflexivity).
      apply Add_inv in Hin as [s HA].
      exists s. split.
      * apply IH. apply Permutation_cons_inv with (a:=x).
        apply (perm_trans HP). apply Permutation_sym. apply Permutation_Add; exact HA.
      * apply inserts_Add; exact HA.
Qed.

Lemma inserts_length : forall x s, length (inserts x s) = S (length s).
Proof.
  intros x s; induction s as [|y t IH]; cbn [inserts length]; [reflexivity|].
  rewrite map_length. cbn [length] in IH. rewrite IH. reflexivity.
Qed.

Lemma in_perms_length : forall L p, In p (perms L) -> length p = length L.
Proof.
  intros L p H. apply perms_correct in H. symmetry. apply Permutation_length; exact H.
Qed.

(* number of permutations is the factorial *)
Fixpoint list_sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + list_sum t end.
Lemma len_flat_map : forall (A B : Type) (h : A -> list B) L,
  length (flat_map h L) = list_sum (map (fun x => length (h x)) L).
Proof. intros A B h L; induction L as [|x t IH]; cbn [flat_map map list_sum]; [reflexivity|];
  rewrite app_length, IH; reflexivity. Qed.
Lemma list_sum_map_const : forall (A : Type) c (l : list A), list_sum (map (fun _ => c) l) = c * length l.
Proof. intros A c l; induction l as [|x t IH]; cbn [map list_sum length]; lia. Qed.
Lemma list_sum_map_ext_in : forall (A : Type) (f g : A -> nat) l,
  (forall a, In a l -> f a = g a) -> list_sum (map f l) = list_sum (map g l).
Proof. intros A f g l H; induction l as [|x t IH]; cbn [map list_sum]; [reflexivity|];
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity| intros a Ha; apply H; right; exact Ha]. Qed.

Lemma length_perms : forall L, length (perms L) = fact (length L).
Proof.
  induction L as [|x t IH]; cbn [perms length fact]; [reflexivity|].
  rewrite len_flat_map.
  rewrite (list_sum_map_ext_in _ (fun s => length (inserts x s)) (fun _ => S (length t))).
  - rewrite list_sum_map_const, IH. reflexivity.
  - intros s Hs. rewrite inserts_length, (in_perms_length t s Hs). reflexivity.
Qed.

(* ---- perms L has no duplicate permutations, when L is NoDup ---- *)
Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) l,
  (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj; induction l as [|x t IH]; intro Hnd; cbn [map]; [constructor|].
  apply NoDup_cons_iff in Hnd as [Hx Ht]. apply NoDup_cons_iff. split.
  - intro Hin. apply in_map_iff in Hin as [y [Hy Hyin]]. apply Hinj in Hy; subst y. contradiction.
  - apply IH; exact Ht.
Qed.

Lemma NoDup_flat_map_disjoint : forall (A B : Type) (f : A -> list B) l,
  NoDup l -> (forall a, In a l -> NoDup (f a)) ->
  (forall a b, In a l -> In b l -> a <> b -> forall q, In q (f a) -> In q (f b) -> False) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l; induction l as [|x t IH]; intros Hnd Heach Hdisj; cbn [flat_map]; [constructor|].
  apply NoDup_cons_iff in Hnd as [Hxt Hndt]. apply NoDup_app.
  - apply Heach; left; reflexivity.
  - apply IH; [exact Hndt | intros a Ha; apply Heach; right; exact Ha |].
    intros a b Ha Hb Hab q Hqa Hqb.
    exact (Hdisj a b (or_intror Ha) (or_intror Hb) Hab q Hqa Hqb).
  - intros q Hq Hq2. apply in_flat_map in Hq2 as [b [Hb Hqb]].
    assert (Hxb : x <> b) by (intro; subst b; contradiction).
    exact (Hdisj x b (or_introl eq_refl) (or_intror Hb) Hxb q Hq Hqb).
Qed.

Fixpoint del (x : nat) (l : list nat) : list nat :=
  match l with [] => [] | y :: t => if y =? x then t else y :: del x t end.
Lemma del_Add : forall x s q, Add x s q -> ~ In x s -> del x q = s.
Proof.
  intros x s q HA; induction HA; intro Hnin; cbn [del].
  - rewrite Nat.eqb_refl. reflexivity.
  - assert (Hne : x0 <> x) by (intro; subst; apply Hnin; left; reflexivity).
    apply Nat.eqb_neq in Hne. rewrite Hne.
    rewrite IHHA; [reflexivity| intro Hc; apply Hnin; right; exact Hc].
Qed.

Lemma not_in_perm : forall x t s, In s (perms t) -> ~ In x t -> ~ In x s.
Proof.
  intros x t s Hs Hxt Hin. apply Hxt.
  apply (Permutation_in x (Permutation_sym (proj1 (perms_correct t s) Hs))). exact Hin.
Qed.

Lemma NoDup_inserts : forall x s, ~ In x s -> NoDup (inserts x s).
Proof.
  intros x s; induction s as [|y t IH]; intro Hnin; cbn [inserts].
  - constructor; [intros []| constructor].
  - assert (x <> y) by (intro; subst; apply Hnin; left; reflexivity).
    apply NoDup_cons_iff. split.
    + intro Hin. apply in_map_iff in Hin as [z [Hz _]]. inversion Hz. subst. contradiction.
    + apply NoDup_map_inj; [intros a b Hab; inversion Hab; reflexivity|].
      apply IH. intro; apply Hnin; right; assumption.
Qed.

Lemma NoDup_perms : forall L, NoDup L -> NoDup (perms L).
Proof.
  induction L as [|x t IH]; intro Hnd; cbn [perms].
  - constructor; [intros []| constructor].
  - apply NoDup_cons_iff in Hnd as [Hxt Hndt].
    apply NoDup_flat_map_disjoint.
    + apply IH; exact Hndt.
    + intros s Hs. apply NoDup_inserts. apply (not_in_perm x t s Hs Hxt).
    + intros s s' Hs Hs' Hneq q Hq Hq'.
      apply inserts_Add in Hq. apply inserts_Add in Hq'.
      pose proof (not_in_perm x t s Hs Hxt) as Hns.
      pose proof (not_in_perm x t s' Hs' Hxt) as Hns'.
      apply Hneq. rewrite <- (del_Add x s q Hq Hns). rewrite <- (del_Add x s' q Hq' Hns'). reflexivity.
Qed.

Print Assumptions perms_correct.
Print Assumptions length_perms.
Print Assumptions NoDup_perms.

(* ===== Stage 2 Part B: counting permutations by their first selected element ===== *)
Require Import Bool.

Fixpoint firstSel (S : nat -> bool) (s : list nat) : option nat :=
  match s with [] => None | x :: t => if S x then Some x else firstSel S t end.
Definition Pfirst (S : nat -> bool) (v : nat) (s : list nat) : bool :=
  match firstSel S s with Some x => x =? v | None => false end.
Definition count_first (S : nat -> bool) (v : nat) (L : list nat) : nat :=
  length (filter (Pfirst S v) (perms L)).

(* helpers *)
Lemma NoDup_filter_nat : forall (P : nat -> bool) l, NoDup l -> NoDup (filter P l).
Proof.
  intros P l; induction l as [|x t IH]; intro Hnd; cbn [filter]; [constructor|].
  apply NoDup_cons_iff in Hnd as [Hin Ht]. destruct (P x).
  - apply NoDup_cons_iff. split; [intro Hc; apply Hin; apply filter_In in Hc as [Hc _]; exact Hc| apply IH; exact Ht].
  - apply IH; exact Ht.
Qed.
Lemma filter_map_comm : forall (A B : Type) (g : A -> B) (P : B -> bool) l,
  filter P (map g l) = map g (filter (fun x => P (g x)) l).
Proof. intros A B g P l; induction l as [|x t IH]; cbn [map filter]; [reflexivity|].
  destruct (P (g x)); cbn [map]; rewrite IH; reflexivity. Qed.
Lemma indic_sum_notin : forall w0 l, ~ In w0 l ->
  list_sum (map (fun w => if w0 =? w then 1 else 0) l) = 0.
Proof.
  intros w0 l; induction l as [|y s IH]; intro Hni; cbn [map list_sum]; [reflexivity|].
  assert (w0 <> y) by (intro; subst; apply Hni; left; reflexivity).
  apply Nat.eqb_neq in H. rewrite H. cbn. apply IH. intro; apply Hni; right; assumption.
Qed.
Lemma nodup_indicator_sum : forall w0 K, NoDup K -> In w0 K ->
  list_sum (map (fun w => if w0 =? w then 1 else 0) K) = 1.
Proof.
  intros w0 K; induction K as [|x t IH]; intros Hnd Hin; [destruct Hin|].
  apply NoDup_cons_iff in Hnd as [Hx Ht]. cbn [map list_sum]. destruct Hin as [Heq|Hin].
  - subst x. rewrite Nat.eqb_refl, (indic_sum_notin w0 t Hx). reflexivity.
  - assert (x <> w0) by (intro; subst; contradiction).
    apply Nat.eqb_neq in H. rewrite Nat.eqb_sym in H. rewrite H. cbn.
    apply IH; [exact Ht| exact Hin].
Qed.

Lemma list_sum_map_add_gen : forall (A : Type) (f g : A -> nat) l,
  list_sum (map (fun a => f a + g a) l) = list_sum (map f l) + list_sum (map g l).
Proof. intros A f g l; induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.

Lemma partition_count : forall (S : nat -> bool) M K,
  NoDup K -> (forall s, In s M -> exists w, In w K /\ firstSel S s = Some w) ->
  length M = list_sum (map (fun w => length (filter (Pfirst S w) M)) K).
Proof.
  intros S M K HndK; induction M as [|s M IH]; intro Hkey.
  - cbn [length filter]. rewrite list_sum_map_const. lia.
  - cbn [length].
    destruct (Hkey s (or_introl eq_refl)) as [w0 [Hw0K Hfs]].
    (* each bucket: filter Pfirst on (s::M); s lands in bucket w0 only *)
    assert (Hbucket : forall w, length (filter (Pfirst S w) (s :: M))
                     = (if w0 =? w then 1 else 0) + length (filter (Pfirst S w) M)).
    { intro w. cbn [filter]. unfold Pfirst at 1. rewrite Hfs.
      destruct (w0 =? w) eqn:E; cbn [length]; reflexivity. }
    rewrite (list_sum_map_ext_in _ (fun w => length (filter (Pfirst S w) (s :: M)))
              (fun w => (if w0 =? w then 1 else 0) + length (filter (Pfirst S w) M)))
      by (intros w _; apply Hbucket).
    rewrite list_sum_map_add_gen.
    rewrite (nodup_indicator_sum w0 K HndK Hw0K).
    rewrite <- (IH (fun s' Hs' => Hkey s' (or_intror Hs'))). reflexivity.
Qed.

Lemma Permutation_filter : forall (A : Type) (f : A -> bool) l l',
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' HP; induction HP; cbn [filter].
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - apply (perm_trans IHHP1 IHHP2).
Qed.
Lemma Permutation_filter_length : forall (A : Type) (f : A -> bool) l l',
  Permutation l l' -> length (filter f l) = length (filter f l').
Proof. intros A f l l' HP. apply Permutation_length, Permutation_filter; exact HP. Qed.

(* value transposition *)
Definition swp (u v x : nat) : nat := if x =? u then v else if x =? v then u else x.
Lemma swp_invol : forall u v x, u <> v -> swp u v (swp u v x) = x.
Proof.
  intros u v x Huv. unfold swp. destruct (x =? u) eqn:Eu.
  - apply Nat.eqb_eq in Eu; subst. destruct (v =? u) eqn:E.
    + apply Nat.eqb_eq in E; subst; contradiction.
    + rewrite Nat.eqb_refl. reflexivity.
  - destruct (x =? v) eqn:Ev.
    + apply Nat.eqb_eq in Ev; subst. rewrite Nat.eqb_refl. reflexivity.
    + rewrite Eu, Ev. reflexivity.
Qed.
Lemma swp_inj : forall u v x y, u <> v -> swp u v x = swp u v y -> x = y.
Proof. intros u v x y Huv H. rewrite <- (swp_invol u v x Huv), <- (swp_invol u v y Huv), H. reflexivity. Qed.
Lemma map_swp_invol : forall u v s, u <> v -> map (swp u v) (map (swp u v) s) = s.
Proof. intros u v s Huv. rewrite map_map. rewrite <- (map_id s) at 2.
  apply map_ext. intro x. apply swp_invol; exact Huv. Qed.
Lemma map_swp_inj : forall u v a b, u <> v -> map (swp u v) a = map (swp u v) b -> a = b.
Proof. intros u v a b Huv H.
  rewrite <- (map_swp_invol u v a Huv), <- (map_swp_invol u v b Huv), H. reflexivity. Qed.
Lemma swp_In : forall u v L, In u L -> In v L -> forall x, In (swp u v x) L <-> In x L.
Proof.
  intros u v L Hu Hv x. unfold swp. destruct (x =? u) eqn:Eu.
  - apply Nat.eqb_eq in Eu; subst. split; auto.
  - destruct (x =? v) eqn:Ev.
    + apply Nat.eqb_eq in Ev; subst. split; auto.
    + reflexivity.
Qed.

Lemma perm_swp_L : forall u v L, NoDup L -> In u L -> In v L -> u <> v ->
  Permutation L (map (swp u v) L).
Proof.
  intros u v L Hnd Hu Hv Huv. apply NoDup_Permutation; [exact Hnd| |].
  - apply NoDup_map_inj; [intros a b Hab; exact (swp_inj u v a b Huv Hab)| exact Hnd].
  - intro x. split; intro Hx.
    + apply in_map_iff. exists (swp u v x). split; [apply swp_invol; exact Huv|].
      apply (swp_In u v L Hu Hv x); exact Hx.
    + apply in_map_iff in Hx as [y [<- Hy]]. apply (swp_In u v L Hu Hv y); exact Hy.
Qed.

Lemma perms_relabel : forall u v L, NoDup L -> In u L -> In v L -> u <> v ->
  Permutation (map (map (swp u v)) (perms L)) (perms L).
Proof.
  intros u v L Hnd Hu Hv Huv. apply NoDup_Permutation.
  - apply NoDup_map_inj; [intros a b Hab; exact (map_swp_inj u v a b Huv Hab)| apply NoDup_perms; exact Hnd].
  - apply NoDup_perms; exact Hnd.
  - intro q. split.
    + intro Hq. apply in_map_iff in Hq as [p [<- Hp]]. apply perms_correct.
      apply perms_correct in Hp.
      apply (perm_trans (perm_swp_L u v L Hnd Hu Hv Huv)). apply Permutation_map; exact Hp.
    + intro Hq. apply perms_correct in Hq. apply in_map_iff.
      exists (map (swp u v) q). split; [apply map_swp_invol; exact Huv|].
      apply perms_correct.
      apply (perm_trans (perm_swp_L u v L Hnd Hu Hv Huv)). apply Permutation_map; exact Hq.
Qed.

Lemma firstSel_map : forall (f : nat -> nat) (S : nat -> bool) s,
  (forall x, S (f x) = S x) -> firstSel S (map f s) = option_map f (firstSel S s).
Proof.
  intros f S s Hpres; induction s as [|x t IH]; cbn [map firstSel]; [reflexivity|].
  rewrite Hpres. destruct (S x); [reflexivity| exact IH].
Qed.

Lemma swp_pres_S : forall (S:nat->bool) u v, S u = true -> S v = true ->
  forall x, S (swp u v x) = S x.
Proof.
  intros S u v Su Sv x. unfold swp. destruct (x =? u) eqn:Eu.
  - apply Nat.eqb_eq in Eu; subst. rewrite Sv, Su; reflexivity.
  - destruct (x =? v) eqn:Ev.
    + apply Nat.eqb_eq in Ev; subst. rewrite Su, Sv; reflexivity.
    + reflexivity.
Qed.

Lemma Pfirst_swap : forall (S:nat->bool) u v s, u <> v -> S u = true -> S v = true ->
  Pfirst S v (map (swp u v) s) = Pfirst S u s.
Proof.
  intros S u v s Huv Su Sv. unfold Pfirst.
  rewrite (firstSel_map (swp u v) S s (swp_pres_S S u v Su Sv)).
  destruct (firstSel S s) as [w|]; [cbn [option_map]| reflexivity].
  destruct (w =? u) eqn:Ew.
  - apply Nat.eqb_eq in Ew; subst. unfold swp. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  - destruct (swp u v w =? v) eqn:Es.
    + (* swp w = v forces w = u, contradiction with Ew *)
      apply Nat.eqb_eq in Es. unfold swp in Es.
      destruct (w =? u) eqn:E1; [discriminate Ew|].
      destruct (w =? v) eqn:E2.
      * apply Nat.eqb_eq in E2; subst. contradiction (Huv (eq_refl)).
      * subst. (* swp gives w = v but E2 says w<>v *) apply Nat.eqb_neq in E2. contradiction.
    + reflexivity.
Qed.

Lemma count_first_swap : forall (S : nat -> bool) L u v,
  NoDup L -> S u = true -> S v = true -> In u L -> In v L ->
  count_first S u L = count_first S v L.
Proof.
  intros S L u v Hnd Su Sv Hu Hv. destruct (u =? v) eqn:Euv.
  - apply Nat.eqb_eq in Euv; subst; reflexivity.
  - apply Nat.eqb_neq in Euv. unfold count_first.
    rewrite <- (Permutation_filter_length _ (Pfirst S v) _ _ (perms_relabel u v L Hnd Hu Hv Euv)).
    rewrite filter_map_comm, map_length.
    apply (f_equal (@length _)). apply filter_ext.
    intro s. symmetry. apply Pfirst_swap; assumption.
Qed.

Lemma firstSel_spec : forall (S:nat->bool) s, (exists y, In y s /\ S y = true) ->
  exists w, firstSel S s = Some w /\ In w s /\ S w = true.
Proof.
  intros S s; induction s as [|x t IH]; intros [y [Hy Sy]]; [destruct Hy|].
  cbn [firstSel]. destruct (S x) eqn:Sx.
  - exists x. split; [reflexivity| split; [left; reflexivity| exact Sx]].
  - destruct Hy as [<-|Hy]; [rewrite Sx in Sy; discriminate|].
    destruct (IH (ex_intro _ y (conj Hy Sy))) as [w [Hfs [Hin Sw]]].
    exists w. split; [exact Hfs| split; [right; exact Hin| exact Sw]].
Qed.

Lemma count_first_value : forall (S : nat -> bool) L v,
  NoDup L -> S v = true -> In v L ->
  length (filter S L) * count_first S v L = fact (length L).
Proof.
  intros S L v Hnd Sv Hv.
  assert (Hpart : fact (length L) = list_sum (map (fun w => count_first S w L) (filter S L))).
  { rewrite <- length_perms. apply (partition_count S (perms L) (filter S L)).
    - apply NoDup_filter_nat; exact Hnd.
    - intros s Hs. apply perms_correct in Hs.
      assert (Hin : In v s) by (apply (Permutation_in v Hs); exact Hv).
      destruct (firstSel_spec S s (ex_intro _ v (conj Hin Sv))) as [w [Hfs [Hws Sw]]].
      exists w. split; [| exact Hfs]. apply filter_In. split; [| exact Sw].
      apply (Permutation_in w (Permutation_sym Hs)); exact Hws. }
  rewrite (list_sum_map_ext_in _ (fun w => count_first S w L) (fun _ => count_first S v L)) in Hpart.
  - rewrite list_sum_map_const in Hpart. lia.
  - intros w Hw. apply filter_In in Hw as [HwL HwS]. apply count_first_swap; auto.
Qed.

Print Assumptions count_first_value.

(* ===== Stage 2 Part B capstone: the quicksort comparison count ===== *)
Definition betw (a b x : nat) : bool := (Nat.min a b <=? x) && (x <=? Nat.max a b).
Definition comparedb (a b : nat) (l : list nat) : bool :=
  match filter (betw a b) l with [] => false | x :: _ => (x =? a) || (x =? b) end.
Definition num_compared (a b n : nat) : nat := length (filter (comparedb a b) (perms (seq 0 n))).

Lemma firstSel_filter_hd : forall (S : nat -> bool) s,
  firstSel S s = match filter S s with [] => None | x :: _ => Some x end.
Proof.
  intros S s; induction s as [|x t IH]; cbn [firstSel filter]; [reflexivity|].
  destruct (S x); [reflexivity| exact IH].
Qed.
Lemma comparedb_Pfirst : forall a b s,
  comparedb a b s = Pfirst (betw a b) a s || Pfirst (betw a b) b s.
Proof.
  intros a b s. unfold comparedb, Pfirst. rewrite firstSel_filter_hd.
  destruct (filter (betw a b) s) as [|x t]; reflexivity.
Qed.
Lemma Pfirst_excl : forall (S:nat->bool) a b s, a <> b -> Pfirst S a s && Pfirst S b s = false.
Proof.
  intros S a b s Hab. unfold Pfirst. destruct (firstSel S s) as [x|]; [|reflexivity].
  destruct (x =? a) eqn:Ea; cbn [andb]; [|reflexivity].
  apply Nat.eqb_eq in Ea; subst. apply Nat.eqb_neq. auto.
Qed.
Lemma length_filter_orb_excl : forall (P Q : list nat -> bool) (l : list (list nat)),
  (forall s, P s && Q s = false) ->
  length (filter (fun s => P s || Q s) l) = length (filter P l) + length (filter Q l).
Proof.
  intros P Q l Hex; induction l as [|x t IH]; [reflexivity|].
  cbn [filter]. pose proof (Hex x) as Hx.
  destruct (P x) eqn:EP; destruct (Q x) eqn:EQ; cbn [orb] in *;
    try discriminate Hx; cbn [length]; rewrite IH; lia.
Qed.

Lemma betw_self_l : forall a b, a < b -> betw a b a = true.
Proof. intros a b H. unfold betw. apply andb_true_iff. split; apply Nat.leb_le.
  - assert (Nat.min a b <= a) by apply Nat.le_min_l. lia.
  - assert (b <= Nat.max a b) by apply Nat.le_max_r. lia. Qed.
Lemma betw_self_r : forall a b, a < b -> betw a b b = true.
Proof. intros a b H. unfold betw. apply andb_true_iff. split; apply Nat.leb_le.
  - assert (Nat.min a b <= a) by apply Nat.le_min_l. lia.
  - assert (b <= Nat.max a b) by apply Nat.le_max_r. lia. Qed.

(* The core counting theorem: the multiplier is the number of interval-values d. *)
Theorem compared_count_raw : forall a b n, a < b -> b < n ->
  length (filter (betw a b) (seq 0 n)) * num_compared a b n = 2 * fact n.
Proof.
  intros a b n Hab Hbn.
  assert (Hnd : NoDup (seq 0 n)) by apply seq_NoDup.
  assert (HinA : In a (seq 0 n)) by (apply in_seq; lia).
  assert (HinB : In b (seq 0 n)) by (apply in_seq; lia).
  assert (Hlen : length (seq 0 n) = n) by apply seq_length.
  unfold num_compared.
  rewrite (filter_ext _ (fun s => Pfirst (betw a b) a s || Pfirst (betw a b) b s))
    by (apply comparedb_Pfirst).
  rewrite length_filter_orb_excl by (intro s; apply Pfirst_excl; lia).
  fold (count_first (betw a b) a (seq 0 n)). fold (count_first (betw a b) b (seq 0 n)).
  rewrite Nat.mul_add_distr_l.
  pose proof (count_first_value (betw a b) (seq 0 n) a Hnd (betw_self_l a b Hab) HinA) as Ha.
  pose proof (count_first_value (betw a b) (seq 0 n) b Hnd (betw_self_r a b Hab) HinB) as Hb.
  rewrite Hlen in Ha, Hb. rewrite Ha, Hb. lia.
Qed.


Lemma filter_none : forall (P : nat -> bool) l, (forall x, In x l -> P x = false) -> filter P l = [].
Proof. intros P l H; induction l as [|x t IH]; cbn [filter]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). apply IH; intros y Hy; apply H; right; exact Hy. Qed.
Lemma filter_all : forall (P : nat -> bool) l, (forall x, In x l -> P x = true) -> filter P l = l.
Proof. intros P l H; induction l as [|x t IH]; cbn [filter]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal. apply IH; intros y Hy; apply H; right; exact Hy. Qed.

Lemma length_filter_betw : forall a b n, a <= b -> b < n ->
  length (filter (betw a b) (seq 0 n)) = S (b - a).
Proof.
  intros a b n Hab Hbn.
  replace n with (a + (S (b - a) + (n - S b))) by lia.
  rewrite seq_app, filter_app.
  rewrite (filter_none (betw a b) (seq 0 a)).
  2:{ intros x Hx. apply in_seq in Hx. unfold betw.
      apply andb_false_iff. left. apply Nat.leb_gt. rewrite Nat.min_l by lia. lia. }
  cbn [app].
  rewrite seq_app, filter_app.
  rewrite (filter_all (betw a b) (seq (0 + a) (S (b - a)))).
  2:{ intros x Hx. apply in_seq in Hx. unfold betw. apply andb_true_iff.
      split; [apply Nat.leb_le; rewrite Nat.min_l by lia; lia
             | apply Nat.leb_le; rewrite Nat.max_r by lia; lia]. }
  rewrite (filter_none (betw a b) (seq (0 + a + S (b - a)) (n - S b))).
  2:{ intros x Hx. apply in_seq in Hx. unfold betw.
      apply andb_false_iff. right. apply Nat.leb_gt. rewrite Nat.max_r by lia. lia. }
  rewrite app_nil_r, seq_length. reflexivity.
Qed.

Theorem compared_count : forall a b n, a < b -> b < n ->
  (b - a + 1) * num_compared a b n = 2 * fact n.
Proof.
  intros a b n Hab Hbn.
  replace (b - a + 1) with (S (b - a)) by lia.
  rewrite <- (length_filter_betw a b n) by lia.
  apply compared_count_raw; assumption.
Qed.

Print Assumptions compared_count.
