(* analysis@home — work unit: records-expected-harmonic (Rocq target).
 *
 * THE DEEP AVERAGE-CASE RESULT. The expected number of left-to-right maxima
 * (records) of a uniformly random permutation of [n] is the harmonic number H_n
 * — the average-case analysis of TAOCP Algorithm M, and the verified twin of the
 * conjecture-track artifact algorithm-m-maxima.json (which ENUMERATES the same
 * means H_n for small n; see the unit's `oracle`).
 *
 * Uniform permutations are modelled by their sequential-rank vectors (Rényi):
 * c = (c_1,...,c_n) with c_i in {1..i}, uniform, |ranks n| = n!. Position i is a
 * record iff c_i = i (the i-th element is the largest of the first i). We do NOT
 * enumerate the n! outcomes: linearity over the LAST coordinate gives the
 * recurrence Tot(S m) = (S m)*Tot m + m! (each of the (S m) choices of the new
 * coordinate keeps the earlier records, and exactly one makes a new record),
 * which in QArith is E[R_n] = E[R_{n-1}] + 1/n, i.e.
 *   records_expected : E records (ranks n) == harmonic n.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint list_sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + list_sum t end.

Lemma list_sum_app : forall a b, list_sum (a ++ b) = list_sum a + list_sum b.
Proof. induction a as [|x t IH]; intro b; cbn [app list_sum]; [reflexivity| rewrite IH; lia]. Qed.

Lemma list_sum_flat_map : forall A (H : A -> list nat) L,
  list_sum (flat_map H L) = list_sum (map (fun x => list_sum (H x)) L).
Proof.
  intros A H L. induction L as [|x t IH]; cbn [flat_map map list_sum]; [reflexivity|].
  rewrite list_sum_app, IH. reflexivity.
Qed.

Lemma map_flat_map : forall A B C (f : B -> C) (g : A -> list B) L,
  map f (flat_map g L) = flat_map (fun x => map f (g x)) L.
Proof.
  intros A B C f g L. induction L as [|x t IH]; cbn [flat_map map]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

Lemma len_flat_map : forall A B (H : A -> list B) L,
  length (flat_map H L) = list_sum (map (fun x => length (H x)) L).
Proof.
  intros A B H L. induction L as [|x t IH]; cbn [flat_map map list_sum]; [reflexivity|].
  rewrite app_length, IH. reflexivity.
Qed.

Lemma list_sum_map_add : forall A (f g : A -> nat) l,
  list_sum (map (fun a => f a + g a) l) = list_sum (map f l) + list_sum (map g l).
Proof. intros A f g l. induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.

Lemma list_sum_map_scale_r : forall A (f : A -> nat) c l,
  list_sum (map (fun a => f a * c) l) = list_sum (map f l) * c.
Proof. intros A f c l. induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.

Lemma list_sum_map_const : forall A c (l : list A), list_sum (map (fun _ => c) l) = c * length l.
Proof. intros A c l. induction l as [|x t IH]; cbn [map list_sum length]; lia. Qed.

Lemma count_absent : forall v l, (forall k, In k l -> k =? v = false) ->
  list_sum (map (fun k => if k =? v then 1 else 0) l) = 0.
Proof.
  intros v l H. induction l as [|x t IH]; cbn [map list_sum]; [reflexivity|].
  rewrite (H x) by (left; reflexivity). rewrite IH; [reflexivity|].
  intros k Hk; apply H; right; exact Hk.
Qed.

Lemma one_hit : forall m, list_sum (map (fun k => if k =? S m then 1 else 0) (seq 1 (S m))) = 1.
Proof.
  intro m. rewrite seq_S, map_app, list_sum_app.
  rewrite count_absent by (intros k Hk; apply in_seq in Hk; apply Nat.eqb_neq; lia).
  cbn [map list_sum].
  assert (Heq : (1 + m =? S m) = true) by (apply Nat.eqb_eq; lia). rewrite Heq. reflexivity.
Qed.

(* ---- the append-friendly record counter ---- *)
Fixpoint rec_from (idx : nat) (c : list nat) : nat :=
  match c with [] => 0 | x :: t => (if x =? idx then 1 else 0) + rec_from (S idx) t end.
Definition records (c : list nat) : nat := rec_from 1 c.

Lemma rec_append : forall c idx k,
  rec_from idx (c ++ [k]) = rec_from idx c + (if k =? idx + length c then 1 else 0).
Proof.
  induction c as [|x t IH]; intros idx k; cbn [app rec_from length].
  - rewrite !Nat.add_0_r. lia.
  - rewrite IH. replace (S idx + length t) with (idx + S (length t)) by lia. lia.
Qed.

Lemma records_append : forall c k,
  records (c ++ [k]) = records c + (if k =? S (length c) then 1 else 0).
Proof.
  intros c k. unfold records. rewrite rec_append.
  replace (1 + length c) with (S (length c)) by lia. reflexivity.
Qed.

(* ---- rank-vector sample space: c_i in {1..i}; |ranks n| = n! ---- *)
Fixpoint ranks (n : nat) : list (list nat) :=
  match n with
  | 0 => [ [] ]
  | S m => flat_map (fun c => map (fun k => c ++ [k]) (seq 1 (S m))) (ranks m)
  end.

Lemma in_ranks_length : forall n c, In c (ranks n) -> length c = n.
Proof.
  induction n as [|m IH]; intros c Hc; cbn [ranks] in Hc.
  - destruct Hc as [<-|[]]. reflexivity.
  - apply in_flat_map in Hc as [c0 [Hc0 Hin]].
    apply in_map_iff in Hin as [k [<- _]]. rewrite app_length. cbn [length].
    rewrite (IH c0 Hc0). lia.
Qed.

Lemma length_ranks : forall n, length (ranks n) = fact n.
Proof.
  induction n as [|m IH]; [reflexivity|]. cbn [ranks]. rewrite len_flat_map.
  assert (E : map (fun c => length (map (fun k => c ++ [k]) (seq 1 (S m)))) (ranks m)
            = map (fun _ => S m) (ranks m)).
  { apply map_ext. intro c. rewrite map_length, seq_length. reflexivity. }
  rewrite E, list_sum_map_const, IH. cbn [fact]. lia.
Qed.

Definition Tot (n : nat) : nat := list_sum (map records (ranks n)).

Lemma Tot_rec : forall m, Tot (S m) = S m * Tot m + fact m.
Proof.
  intro m. unfold Tot. cbn [ranks]. rewrite map_flat_map, list_sum_flat_map.
  assert (E : map (fun c => list_sum (map records (map (fun k => c ++ [k]) (seq 1 (S m))))) (ranks m)
            = map (fun c => records c * S m + 1) (ranks m)).
  { apply map_ext_in. intros c Hc. rewrite map_map.
    assert (E2 : map (fun k => records (c ++ [k])) (seq 1 (S m))
               = map (fun k => records c + (if k =? S m then 1 else 0)) (seq 1 (S m))).
    { apply map_ext_in. intros k _. rewrite records_append, (in_ranks_length m c Hc). reflexivity. }
    rewrite E2, list_sum_map_add, list_sum_map_const, seq_length, one_hit. reflexivity. }
  rewrite E, list_sum_map_add, list_sum_map_scale_r, (list_sum_map_const _ 1 (ranks m)), length_ranks.
  fold (Tot m). lia.
Qed.

(* ---- rational expectation = the harmonic number ---- *)
Require Import QArith ZArith Factorial.
Open Scope Q_scope.

Fixpoint harmonic (n : nat) : Q :=
  match n with O => 0 | S m => harmonic m + 1 / inject_Z (Z.of_nat (S m)) end.

Definition E (f : list nat -> nat) (l : list (list nat)) : Q :=
  inject_Z (Z.of_nat (list_sum (map f l))) / inject_Z (Z.of_nat (length l)).

Lemma inj_nz : forall n, (0 < n)%nat -> ~ inject_Z (Z.of_nat n) == 0.
Proof. intros n Hn Heq. unfold Qeq in Heq; simpl in Heq; lia. Qed.

Lemma Tot_harmonic : forall n,
  inject_Z (Z.of_nat (Tot n)) / inject_Z (Z.of_nat (fact n)) == harmonic n.
Proof.
  induction n as [|m IH].
  - reflexivity.
  - rewrite Tot_rec. cbn [fact harmonic].
    assert (Ha : ~ inject_Z (Z.of_nat (S m)) == 0) by (apply inj_nz; lia).
    assert (Hf : ~ inject_Z (Z.of_nat (fact m)) == 0) by (apply inj_nz; apply lt_O_fact).
    rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, inject_Z_plus, !inject_Z_mult.
    rewrite <- IH. field. split; assumption.
Qed.

Theorem records_expected : forall n, E records (ranks n) == harmonic n.
Proof. intro n. unfold E. fold (Tot n). rewrite length_ranks. apply Tot_harmonic. Qed.
