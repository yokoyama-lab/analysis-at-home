(* analysis@home — average-case cost framework (seed).
 *
 * A reusable discipline for machine-checked AVERAGE-CASE cost: an algorithm is
 * instrumented with an operation counter, the input distribution is a finite
 * (here: uniform) family of inputs, and the EXPECTED cost is first-class.
 *
 *   mean_eq costs p q  :=  q * Σcosts = p * |costs|       (division-free "E = p/q")
 *   expect costs : Q   :=  (Σcosts) / |costs|             (the rational mean)
 *   mean_eq_expect     :  mean_eq costs p q -> expect costs == p / q   (bridge)
 *
 * Every algorithm discharges a nat `mean_eq`; the rational expectation follows
 * for free. The conjecture track (tools/conjecture/) computes the same E[cost]
 * by exhaustive enumeration and serves as a property-based ORACLE that the
 * statement is faithful before it is proved (see tools/oracle_check.py).
 *
 * First instance: linear search for a uniformly random present target —
 * E[comparisons] = (n+1)/2 — derived through the framework, grounded in the
 * instrumented counter `lc`.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint list_sum (l : list nat) : nat :=
  match l with [] => 0 | x :: t => x + list_sum t end.

(* framework primitive: the average of the per-outcome costs is exactly p/q *)
Definition mean_eq (costs : list nat) (p q : nat) : Prop :=
  (q * list_sum costs = p * length costs)%nat.

(* instrumented linear search: number of comparisons to find `key` *)
Fixpoint lc (key : nat) (l : list nat) : nat :=
  match l with [] => 0 | x :: t => if x =? key then 1 else S (lc key t) end.

Lemma lc_seq : forall m a k, a <= k < a + m -> lc k (seq a m) = S (k - a).
Proof.
  induction m as [|m IH]; intros a k H; cbn [seq lc]; [lia|].
  destruct (a =? k) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply Nat.eqb_neq in E. rewrite (IH (S a) k) by lia. lia.
Qed.

Lemma list_sum_app : forall l x, list_sum (l ++ [x]) = list_sum l + x.
Proof. intros l x; induction l as [|y t IH]; cbn [list_sum app]; lia. Qed.

Lemma sum_seq1 : forall n, 2 * list_sum (seq 1 n) = n * (n + 1).
Proof.
  induction n as [|n IH]; [reflexivity|]. rewrite seq_S, list_sum_app. nia.
Qed.

(* E[comparisons] of linear search for a uniformly random present target = (n+1)/2 *)
Theorem linear_search_avg :
  forall n, mean_eq (map (fun k => lc k (seq 1 n)) (seq 1 n)) (n + 1) 2.
Proof.
  intro n. unfold mean_eq. rewrite map_length, seq_length.
  assert (Hmap : map (fun k => lc k (seq 1 n)) (seq 1 n) = seq 1 n).
  { transitivity (map (fun k => k) (seq 1 n)).
    - apply map_ext_in. intros k Hk. apply in_seq in Hk. rewrite (lc_seq n 1 k) by lia. lia.
    - induction (seq 1 n) as [|a t IHt]; [reflexivity|]. cbn [map]. rewrite IHt. reflexivity. }
  rewrite Hmap, sum_seq1. lia.
Qed.

(* ---------- rational expectation: the Q bridge, proved once ---------- *)
Require Import QArith ZArith.
Open Scope Q_scope.

Definition expect (costs : list nat) : Q :=
  inject_Z (Z.of_nat (list_sum costs)) / inject_Z (Z.of_nat (length costs)).

Lemma Qdiv_cross : forall a b c d, ~ b == 0 -> ~ d == 0 -> a * d == c * b -> a / b == c / d.
Proof.
  intros a b c d Hb Hd H.
  apply (proj1 (Qmult_inj_r (a / b) (c / d) b Hb)).
  rewrite (Qmult_comm (a / b) b), Qmult_div_r by exact Hb.
  apply (proj1 (Qmult_inj_r a (c / d * b) d Hd)).
  rewrite (Qmult_comm (c / d) b), <- Qmult_assoc, (Qmult_comm (c / d) d), Qmult_div_r by exact Hd.
  rewrite (Qmult_comm b c). exact H.
Qed.

Lemma inject_nat_nz : forall n, (0 < n)%nat -> ~ inject_Z (Z.of_nat n) == 0.
Proof. intros n Hn Heq. unfold Qeq in Heq. simpl in Heq. lia. Qed.

Lemma mean_eq_expect : forall costs p q,
  (0 < q)%nat -> (0 < length costs)%nat -> mean_eq costs p q ->
  expect costs == inject_Z (Z.of_nat p) / inject_Z (Z.of_nat q).
Proof.
  intros costs p q Hq Hl Hm. unfold expect.
  apply Qdiv_cross; [apply inject_nat_nz; lia | apply inject_nat_nz; lia | ].
  rewrite <- !inject_Z_mult, <- !Nat2Z.inj_mul.
  assert (Hs : (list_sum costs * q = p * length costs)%nat) by (unfold mean_eq in Hm; nia).
  rewrite Hs. reflexivity.
Qed.

(* the rational expected comparison count of linear search is exactly (n+1)/2 *)
Corollary linear_search_expect : forall n, (0 < n)%nat ->
  expect (map (fun k => lc k (seq 1 n)) (seq 1 n))
    == inject_Z (Z.of_nat (n + 1)) / inject_Z (Z.of_nat 2).
Proof.
  intros n Hn. apply mean_eq_expect.
  - lia.
  - rewrite map_length, seq_length. exact Hn.
  - apply linear_search_avg.
Qed.
