(* analysis@home -- work unit: quicksort-average-comparisons (Rocq target, STAGE 2 PART A).
 *
 * The linearity-of-expectation derivation of the quicksort average reaches the
 * closed form through the pair-distance sum:
 *   E[C] = Sum_{i<j} 2/(j-i+1) = 2 * Sum_{d=2}^{n} (n+1-d)/d = 2(n+1)H_n - 4n,
 * because there are (n+1-d) value-pairs at interval distance d. This file proves
 * the arithmetic backbone of that derivation in QArith, axiom-free:
 *   quicksort_pairsum_closed : 1<=n -> 2 * psum n == 2*q(n+1)*H n - 4*q n,
 * where psum n = Sum_{d=2}^{n} (n+1-d)/d. Combined with Quicksort.v's program-level
 * pair-decomposition cmp_eq_pairsum and the (small-n verified) count 2*n!/d, this is
 * the complete chain program -> pairs -> closed form modulo the one general counting
 * lemma (Part B; see Quicksort.v num_compared / Totpairs and statement.md).
 *
 * VERIFIED (Print Assumptions quicksort_pairsum_closed: closed under the global context). *)

(* Stage 2, Part A: the linearity-of-expectation arithmetic backbone.
   pairdist sum  Sum_{d=2}^{n} (n+1-d)/d  equals the closed form 2(n+1)H_n - 4n
   (divided by 2). This is E[C] = Sum_{i<j} 2/(j-i+1) collapsed by interval
   distance d = j-i+1: there are (n+1-d) value-pairs at distance d. *)
Require Import QArith ZArith Arith Lia List.
Import ListNotations.
Open Scope Q_scope.

Definition q (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma q_pos : forall n, (0 < n)%nat -> 0 < q n.
Proof. intros n Hn. unfold q. unfold Qlt; simpl. lia. Qed.
Lemma q_nonzero : forall n, (0 < n)%nat -> ~ q n == 0.
Proof. intros n Hn Hc. apply (Qlt_irrefl 0). rewrite <- Hc at 2. apply q_pos; exact Hn. Qed.
Lemma inject_Z_minus : forall x y, inject_Z (x - y) == inject_Z x - inject_Z y.
Proof. intros x y.
  assert (Hh : inject_Z (x - y) + inject_Z y == inject_Z x).
  { rewrite <- inject_Z_plus. f_equiv. ring. }
  rewrite <- Hh. ring. Qed.
Lemma q_sub : forall a b, (b <= a)%nat -> q (a - b) == q a - q b.
Proof. intros a b Hle. unfold q. rewrite Nat2Z.inj_sub by exact Hle. rewrite inject_Z_minus. reflexivity. Qed.

Fixpoint H (n : nat) : Q := match n with O => 0 | S m => H m + / q (S m) end.

Fixpoint lsumQ (l : list Q) : Q := match l with [] => 0 | x :: t => x + lsumQ t end.
Lemma lsumQ_map_add : forall (A:Type) (f g : A -> Q) l,
  lsumQ (map (fun a => f a + g a) l) == lsumQ (map f l) + lsumQ (map g l).
Proof. intros A f g l; induction l as [|x t IH]; simpl; [ring|]. rewrite IH; ring. Qed.
Lemma lsumQ_map_scale : forall (A:Type) (c:Q) (f : A -> Q) l,
  lsumQ (map (fun a => c * f a) l) == c * lsumQ (map f l).
Proof. intros A c f l; induction l as [|x t IH]; simpl; [ring|]. rewrite IH; ring. Qed.
Lemma lsumQ_ext : forall (A:Type) (f g : A -> Q) l,
  (forall a, In a l -> f a == g a) -> lsumQ (map f l) == lsumQ (map g l).
Proof. intros A f g l Hfg; induction l as [|x t IH]; simpl; [reflexivity|].
  rewrite (Hfg x (or_introl eq_refl)), IH; [reflexivity| intros a Ha; apply Hfg; right; exact Ha]. Qed.
Lemma lsumQ_map_const1 : forall (A:Type) (l:list A), lsumQ (map (fun _ => 1) l) == q (length l).
Proof. intros A l; induction l as [|x t IH]; simpl; [reflexivity|].
  rewrite IH. unfold q. rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l, inject_Z_plus. ring. Qed.

(* harmonic tail: Sum_{d=2}^{n} 1/d = H_n - 1, for n >= 1 *)
Lemma H_seq1 : forall n, lsumQ (map (fun d => / q d) (seq 1 n)) == H n.
Proof.
  induction n as [|m IH]; [reflexivity|].
  rewrite seq_S, map_app. simpl (map _ _).
  (* lsumQ (a ++ [x]) = lsumQ a + x *)
  assert (Happ : forall a b, lsumQ (a ++ b) == lsumQ a + lsumQ b).
  { intros a b; induction a as [|y t IHa]; simpl; [ring|]. rewrite IHa; ring. }
  rewrite Happ. simpl. rewrite IH. simpl. ring.
Qed.

Lemma harmonic_tail : forall n, (1 <= n)%nat ->
  lsumQ (map (fun d => / q d) (seq 2 (n - 1))) == H n - 1.
Proof.
  intros n Hn. destruct n as [|m]; [lia|].
  replace (S m - 1)%nat with m by lia.
  (* seq 1 (S m) = 1 :: seq 2 m *)
  assert (Hs : seq 1 (S m) = 1%nat :: seq 2 m).
  { simpl. reflexivity. }
  pose proof (H_seq1 (S m)) as Hh. rewrite Hs in Hh. simpl in Hh.
  (* Hh : / q 1 + lsumQ (map .. (seq 2 m)) == H (S m) *)
  assert (Hq1 : / q 1 == 1) by reflexivity.
  rewrite Hq1 in Hh. rewrite <- Hh. ring.
Qed.

Definition psum (n : nat) : Q := lsumQ (map (fun d => q (n + 1 - d) / q d) (seq 2 (n - 1))).

(* per-term split: (n+1-d)/d = (n+1)/d - 1, valid for 2 <= d <= n *)
Lemma psum_split : forall n, (1 <= n)%nat ->
  psum n == q (n+1) * lsumQ (map (fun d => / q d) (seq 2 (n-1))) - q (n - 1).
Proof.
  intros n Hn. unfold psum.
  rewrite (lsumQ_ext _ (fun d => q (n+1-d) / q d)
                       (fun d => q (n+1) * / q d - 1)).
  - rewrite (lsumQ_ext _ (fun d => q (n+1) * / q d - 1)
                         (fun d => q (n+1) * / q d + (-1) * 1)) by (intros; ring).
    rewrite lsumQ_map_add, lsumQ_map_scale, lsumQ_map_scale, lsumQ_map_const1.
    rewrite seq_length. ring.
  - intros d Hd. apply in_seq in Hd.
    assert (Hdn : (d <= n)%nat) by lia.
    assert (Hd1 : (1 <= d)%nat) by lia.
    rewrite q_sub by lia.
    field. apply q_nonzero; lia.
Qed.

Theorem quicksort_pairsum_closed : forall n, (1 <= n)%nat ->
  2 * psum n == 2 * q (n + 1) * H n - 4 * q n.
Proof.
  intros n Hn. rewrite psum_split by exact Hn. rewrite harmonic_tail by exact Hn.
  rewrite q_sub by lia.
  (* now pure field identity in q n, q(n+1), H n *)
  assert (E1 : q (n+1) == q n + 1).
  { replace (n+1)%nat with (S n) by lia. unfold q. rewrite Nat2Z.inj_succ.
    unfold Z.succ. rewrite inject_Z_plus. reflexivity. }
  assert (Hq1 : q 1 == 1) by reflexivity. rewrite Hq1.
  rewrite E1. ring.
Qed.

Print Assumptions quicksort_pairsum_closed.
