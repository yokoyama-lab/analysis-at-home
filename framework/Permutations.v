(* analysis@home framework: permutation-enumeration infrastructure (axiom-free).
 *
 * The average-case framework repeatedly sums a cost over "every permutation of an
 * input". This file makes that rigorous and reusable: the generator `perms` lists
 * every permutation of its argument EXACTLY ONCE, which is the content of
 *   perms_correct : In p (perms L) <-> Permutation L p
 *   length_perms  : length (perms L) = fact (length L)
 *   NoDup_perms   : NoDup L -> NoDup (perms L)
 * plus the supporting `inserts`/`Add` correspondence (inserts_Add) and the
 * deletion inverse (del_Add). These are the foundation for the quicksort Stage-2
 * counting lemma (a fixed value-pair at interval distance d is compared in 2*n!/d
 * permutations -- the "first element of a subset of a uniform permutation is
 * uniform" fact that measure-theoretic developments get for free, proved here as
 * an explicit combinatorial bijection). Records/collisions enumerate permutations
 * too and can reuse this.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

(* Reusable permutation-enumeration infrastructure for the average-case framework:
   the generator `perms` lists every permutation of its input exactly once. *)
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
