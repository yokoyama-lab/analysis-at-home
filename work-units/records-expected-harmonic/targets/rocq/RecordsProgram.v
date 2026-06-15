(* analysis@home -- work unit: records-expected-harmonic (Rocq target, PROGRAM GROUNDING).
 *
 * Companion to Records.v (which models a uniform permutation by Renyi rank vectors).
 * This file grounds the SAME average -- E[#records] = H_n -- in an INSTRUMENTED
 * PROGRAM run over ACTUAL permutations, and DEMONSTRATES REUSE of the shared
 * average-case library framework/Permutations.v (Require Import Permutations):
 *
 *   records : an operational left-to-right-maxima counter (records_op).
 *   records_op_sum : records s = sum over v of [v is the first element >= v in s]
 *                    -- value v is a left-to-right maximum iff it precedes every
 *                    larger value, i.e. v = firstSel (>= v) s. This recasts records
 *                    as the framework's Pfirst, so the counting reduces to the
 *                    library's count_first_value (no bespoke combinatorics here).
 *   records_program_expected : expect_records n == harmonic n, axiom-free,
 *                    where expect_records n = (sum over perms of records) / n!.
 *
 * The H_n falls straight out of count_first_value: a value v is the first among the
 * (n-v) values >= v with probability 1/(n-v), so E = sum_{v<n} 1/(n-v) = H_n. This
 * is the framework paying off -- a second classic average reusing one lemma.
 *
 * VERIFIED (Print Assumptions records_program_expected: closed under the global context). *)

Require Import List Arith Lia Permutation.
Require Import Permutations.
Import ListNotations.

Definition beats (mo : option nat) (v : nat) : bool :=
  match mo with None => true | Some m => m <? v end.
Definition upd (mo : option nat) (v : nat) : option nat :=
  match mo with None => Some v | Some m => Some (Nat.max m v) end.
Fixpoint records_op (mo : option nat) (s : list nat) : nat :=
  match s with
  | [] => 0
  | x :: t => (if beats mo x then 1 else 0) + records_op (upd mo x) t
  end.
Definition records (s : list nat) : nat := records_op None s.

Definition ge (v x : nat) : bool := v <=? x.
Definition recb (mo : option nat) (s : list nat) (v : nat) : nat :=
  if beats mo v then (if Pfirst (ge v) v s then 1 else 0) else 0.

Lemma Pfirst_self_head : forall v t, Pfirst (ge v) v (v :: t) = true.
Proof. intros v t. unfold Pfirst, ge. cbn [firstSel]. rewrite Nat.leb_refl. cbn. apply Nat.eqb_refl. Qed.
Lemma Pfirst_ge_skip : forall v x t, x < v -> Pfirst (ge v) v (x :: t) = Pfirst (ge v) v t.
Proof. intros v x t H. unfold Pfirst, ge. cbn [firstSel].
  replace (v <=? x) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. Qed.
Lemma Pfirst_ge_block : forall v x t, v < x -> Pfirst (ge v) v (x :: t) = false.
Proof. intros v x t H. unfold Pfirst, ge. cbn [firstSel].
  replace (v <=? x) with true by (symmetry; apply Nat.leb_le; lia). cbn.
  apply Nat.eqb_neq. lia. Qed.

Lemma records_op_sum : forall s mo, NoDup s ->
  records_op mo s = list_sum (map (recb mo s) s).
Proof.
  induction s as [|x t IH]; intros mo Hnd; [reflexivity|].
  apply NoDup_cons_iff in Hnd as [Hxt Hndt].
  cbn [records_op map list_sum].
  assert (Hhead : recb mo (x :: t) x = if beats mo x then 1 else 0).
  { unfold recb. rewrite Pfirst_self_head. reflexivity. }
  rewrite Hhead, (IH (upd mo x) Hndt). f_equal.
  apply list_sum_map_ext_in. intros v Hv.
  assert (Hvx : v <> x) by (intro; subst; contradiction).
  unfold recb. destruct (lt_eq_lt_dec x v) as [[Hxv|Hxv]|Hxv]; [|exfalso;auto|].
  - (* x < v : skip; beats agree *)
    rewrite (Pfirst_ge_skip v x t Hxv).
    assert (Hbe : beats (upd mo x) v = beats mo v).
    { unfold upd, beats. destruct mo as [m|].
      - apply Bool.eq_true_iff_eq; split; intro H; apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
      - apply Nat.ltb_lt; lia. }
    rewrite Hbe. reflexivity.
  - (* v < x : block (term 0); beats (upd) v false *)
    rewrite (Pfirst_ge_block v x t Hxv).
    assert (Hb : beats (upd mo x) v = false).
    { unfold upd, beats. destruct mo as [m|]; apply Nat.ltb_ge; lia. }
    rewrite Hb. destruct (beats mo v); reflexivity.
Qed.

(* ---- sum over all permutations: reuse count_first_value from the framework ---- *)
Lemma list_sum_Perm : forall l l', Permutation l l' -> list_sum l = list_sum l'.
Proof. intros l l' HP; induction HP; cbn [list_sum]; lia. Qed.
Lemma sum_indicator_filter : forall (A:Type) (P:A->bool) l,
  list_sum (map (fun a => if P a then 1 else 0) l) = length (filter P l).
Proof. intros A P l; induction l as [|x t IH]; cbn [map list_sum filter]; [reflexivity|].
  destruct (P x); cbn [length list_sum]; lia. Qed.
Lemma list_sum_swap : forall (A B:Type) (f:A->B->nat) M K,
  list_sum (map (fun a => list_sum (map (f a) K)) M)
  = list_sum (map (fun k => list_sum (map (fun a => f a k) M)) K).
Proof.
  intros A B f M K; induction M as [|a M IH]; cbn [map list_sum].
  - induction K as [|k K IHk]; cbn [map list_sum]; [reflexivity|]. rewrite <- IHk; reflexivity.
  - rewrite IH. rewrite <- list_sum_map_add_gen. apply list_sum_map_ext_in. intros k _. reflexivity.
Qed.

Definition Tot_records (n : nat) : nat := list_sum (map records (perms (seq 0 n))).

Lemma Tot_records_count : forall n,
  Tot_records n = list_sum (map (fun v => count_first (ge v) v (seq 0 n)) (seq 0 n)).
Proof.
  intro n. unfold Tot_records.
  (* records sigma = sum over v in seq 0 n of recb None sigma v *)
  rewrite (list_sum_map_ext_in _ records
            (fun s => list_sum (map (recb None s) (seq 0 n)))).
  2:{ intros s Hs. apply perms_correct in Hs.
      unfold records. rewrite (records_op_sum s None).
      2:{ apply (Permutation_NoDup Hs). apply seq_NoDup. }
      apply list_sum_Perm. apply Permutation_map. apply Permutation_sym; exact Hs. }
  (* Fubini: swap perms and seq 0 n *)
  rewrite (list_sum_swap _ _ (recb None) (perms (seq 0 n)) (seq 0 n)).
  apply list_sum_map_ext_in. intros v _.
  (* sum over perms of recb None s v = count_first (ge v) v (seq 0 n) *)
  unfold count_first.
  rewrite <- sum_indicator_filter.
  apply list_sum_map_ext_in. intros s _. unfold recb. cbn [beats]. reflexivity.
Qed.

(* number of values >= v in {0..n-1} is n - v *)
Lemma filter_none' : forall (P : nat -> bool) l, (forall x, In x l -> P x = false) -> filter P l = [].
Proof. intros P l H; induction l as [|x t IH]; cbn [filter]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). apply IH; intros y Hy; apply H; right; exact Hy. Qed.
Lemma filter_all' : forall (P : nat -> bool) l, (forall x, In x l -> P x = true) -> filter P l = l.
Proof. intros P l H; induction l as [|x t IH]; cbn [filter]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal. apply IH; intros y Hy; apply H; right; exact Hy. Qed.
Lemma length_filter_ge : forall v n, v <= n -> length (filter (ge v) (seq 0 n)) = n - v.
Proof.
  intros v n Hvn. replace n with (v + (n - v)) by lia.
  rewrite seq_app, filter_app.
  rewrite (filter_none' (ge v) (seq 0 v)).
  2:{ intros x Hx. apply in_seq in Hx. unfold ge. apply Nat.leb_gt. lia. }
  rewrite (filter_all' (ge v) (seq (0 + v) (n - v))).
  2:{ intros x Hx. apply in_seq in Hx. unfold ge. apply Nat.leb_le. lia. }
  cbn [app]. rewrite seq_length. lia.
Qed.

(* the key nat identity, via the framework's count_first_value *)
Lemma records_count_value : forall n v, v < n ->
  (n - v) * count_first (ge v) v (seq 0 n) = fact n.
Proof.
  intros n v Hvn.
  pose proof (count_first_value (ge v) (seq 0 n) v (seq_NoDup n 0)) as Hc.
  rewrite length_filter_ge in Hc by lia. rewrite seq_length in Hc.
  apply Hc; [unfold ge; apply Nat.leb_le; lia | apply in_seq; lia].
Qed.

Require Import QArith ZArith.
Open Scope Q_scope.

Definition q (n : nat) : Q := inject_Z (Z.of_nat n).
Lemma q_add : forall a b, q (a + b)%nat == q a + q b.
Proof. intros a b. unfold q. rewrite Nat2Z.inj_add, inject_Z_plus. reflexivity. Qed.
Lemma q_mul : forall a b, q (a * b)%nat == q a * q b.
Proof. intros a b. unfold q. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity. Qed.
Lemma q_pos : forall n, (0 < n)%nat -> 0 < q n.
Proof. intros n Hn. unfold q, Qlt; simpl. lia. Qed.
Lemma q_nz : forall n, (0 < n)%nat -> ~ q n == 0.
Proof. intros n Hn Hc. apply (Qlt_irrefl 0). rewrite <- Hc at 2. apply q_pos; exact Hn. Qed.

Fixpoint harmonic (n : nat) : Q := match n with O => 0 | S m => harmonic m + / q (S m) end.

Fixpoint lsumQ (l : list Q) : Q := match l with [] => 0 | x :: t => x + lsumQ t end.
Lemma lsumQ_app : forall a b, lsumQ (a ++ b) == lsumQ a + lsumQ b.
Proof. induction a; intro b; cbn [app lsumQ]; [ring| rewrite IHa; ring]. Qed.
Lemma q_list_sum : forall l, q (list_sum l) == lsumQ (map q l).
Proof. induction l as [|x t IH]; cbn [list_sum map lsumQ]; [reflexivity|]. rewrite q_add, IH; reflexivity. Qed.
Lemma lsumQ_ext : forall (A:Type)(f g:A->Q) l, (forall a, In a l -> f a == g a) ->
  lsumQ (map f l) == lsumQ (map g l).
Proof. intros A f g l H; induction l as [|x t IH]; cbn [map lsumQ]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity| intros a Ha; apply H; right; exact Ha]. Qed.
Lemma lsumQ_scale : forall (A:Type)(c:Q)(f:A->Q) l, lsumQ (map (fun a => c * f a) l) == c * lsumQ (map f l).
Proof. intros A c f l; induction l as [|x t IH]; cbn [map lsumQ]; [ring| rewrite IH; ring]. Qed.

Lemma harmonic_reindex : forall (n:nat),
  lsumQ (map (fun v => / q (n - v)) (seq 0 n)) == harmonic n.
Proof.
  induction n as [|m IH]; [reflexivity|].
  cbn [seq]. cbn [map lsumQ].
  rewrite Nat.sub_0_r.
  (* seq 1 m = map S (seq 0 m); rewrite the tail *)
  replace (seq 1 m) with (map S (seq 0 m)) by (rewrite <- seq_shift; reflexivity).
  rewrite map_map.
  rewrite (lsumQ_ext _ (fun x => / q (S m - S x)) (fun x => / q (m - x)))
    by (intros x _; rewrite Nat.sub_succ; reflexivity).
  rewrite IH. cbn [harmonic]. ring.
Qed.

Lemma q_count_term : forall (n v : nat), (v < n)%nat ->
  q (count_first (ge v) v (seq 0 n)) == q (fact n) * / q (n - v).
Proof.
  intros n v Hvn.
  assert (Hnz : ~ q (n - v) == 0) by (apply q_nz; lia).
  assert (H1 : q (n - v) * q (count_first (ge v) v (seq 0 n)) == q (fact n)).
  { rewrite <- q_mul. rewrite (records_count_value n v Hvn). reflexivity. }
  rewrite <- H1. field. exact Hnz.
Qed.

Definition expect_records (n : nat) : Q := q (Tot_records n) / q (fact n).

Theorem records_program_expected : forall (n:nat), expect_records n == harmonic n.
Proof.
  intro n. unfold expect_records.
  assert (Hfn : ~ q (fact n) == 0) by (apply q_nz; apply lt_O_fact).
  assert (Hnum : q (Tot_records n) == q (fact n) * harmonic n).
  { rewrite Tot_records_count, q_list_sum, map_map.
    rewrite (lsumQ_ext _ (fun v => q (count_first (ge v) v (seq 0 n)))
                         (fun v => q (fact n) * / q (n - v))).
    2:{ intros v Hv. apply in_seq in Hv. apply q_count_term. lia. }
    rewrite lsumQ_scale, harmonic_reindex. reflexivity. }
  rewrite Hnum. field. exact Hfn.
Qed.


Print Assumptions records_program_expected.
