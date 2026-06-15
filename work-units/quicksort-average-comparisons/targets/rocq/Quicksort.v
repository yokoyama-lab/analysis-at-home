(* analysis@home -- work unit: quicksort-average-comparisons (Rocq target, PROGRAM GROUNDING).
 *
 * Companion to QuicksortAverage.v (which proves the recurrence's solution equals
 * the closed form 2(n+1)H_n-4n). That file is a recurrence, not a program. THIS
 * file closes the "cost is a combinatorial proxy, not a program's cost" gap: it
 * defines an INSTRUMENTED head-pivot quicksort comparison counter `cmp` on actual
 * lists and proves two things, axiom-free.
 *
 *  (M1) cmp is a real comparison counter with the partition recurrence
 *       cmp (p::xs) = |xs| + cmp (xs<p) + cmp (xs>p)   [cmp_cons]
 *       and summed over EVERY permutation of {0..n-1} it reproduces the closed
 *       form's small values (mean * n!): Tot 2..6 = 2,16,116,888,7416 [vm_compute].
 *
 *  (M2) THE PAIR-DECOMPOSITION IDENTITY (the compositional core):
 *       cmp l = #{ pairs of elements that ever get directly compared }   [cmp_eq_pairsum]
 *       i.e. cmp l = pairsum l, where two values are "compared" iff, among the
 *       elements whose value lies in their closed interval, the first one in the
 *       input is one of the two. This is exactly the linearity-of-expectation
 *       decomposition E[C] = Sum_{i<j} P[i,j compared] expressed at the PROGRAM
 *       level, proved by structural case analysis on the pivot -- no probability,
 *       no enumeration of the n! inputs. It is the program-grounded heart of the
 *       average-case analysis and is the seam (see docs/research-avg-cost.md) that
 *       distinguishes this from a bespoke recurrence/Giry-monad proof.
 *
 * What remains (Stage 2, see statement.md): the analytic step from the pair
 * decomposition to the closed form -- summing pairsum over all permutations and
 * showing a fixed value-pair at interval-distance d is compared in exactly
 * n!*2/d permutations, hence E[C] = Sum_{d=2}^{n} (n-d+1)*2/d = 2(n+1)H_n-4n.
 *
 * VERIFIED (Print Assumptions cmp_eq_pairsum: closed under the global context). *)

Require Import List Arith Lia Bool.
Import ListNotations.

(* ===== M1: instrumented head-pivot quicksort comparison counter ===== *)
Fixpoint cmpf (fuel : nat) (l : list nat) : nat :=
  match fuel with
  | O => 0
  | S f =>
    match l with
    | [] => 0
    | p :: xs => length xs + cmpf f (filter (fun x => x <? p) xs)
                           + cmpf f (filter (fun x => p <? x) xs)
    end
  end.
Definition cmp (l : list nat) : nat := cmpf (length l) l.

Lemma filter_length_le : forall (P : nat -> bool) l, length (filter P l) <= length l.
Proof. intros P l; induction l as [|x t IH]; cbn [filter length]; [lia|];
  destruct (P x); cbn [length]; lia. Qed.

Lemma cmpf_irr : forall n f g l,
  length l <= n -> length l <= f -> length l <= g -> cmpf f l = cmpf g l.
Proof.
  induction n as [|n IH]; intros f g l Hn Hf Hg.
  - destruct l as [|x t]; cbn [length] in *; [|lia]. destruct f, g; reflexivity.
  - destruct l as [|p xs]; cbn [length] in *.
    + destruct f, g; reflexivity.
    + destruct f as [|f]; [lia|]. destruct g as [|g]; [lia|]. cbn [cmpf].
      pose proof (filter_length_le (fun x => x <? p) xs) as Hlo.
      pose proof (filter_length_le (fun x => p <? x) xs) as Hhi.
      rewrite (IH f g (filter (fun x => x <? p) xs)) by lia.
      rewrite (IH f g (filter (fun x => p <? x) xs)) by lia. reflexivity.
Qed.

Lemma cmp_cons : forall p xs,
  cmp (p :: xs) = length xs + cmp (filter (fun x => x <? p) xs)
                            + cmp (filter (fun x => p <? x) xs).
Proof.
  intros p xs. unfold cmp at 1. cbn [length cmpf]. unfold cmp.
  pose proof (filter_length_le (fun x => x <? p) xs) as Hlo.
  pose proof (filter_length_le (fun x => p <? x) xs) as Hhi.
  rewrite (cmpf_irr (length xs) (length xs) (length (filter (fun x => x <? p) xs))) by lia.
  rewrite (cmpf_irr (length xs) (length xs) (length (filter (fun x => p <? x) xs))) by lia.
  reflexivity.
Qed.

(* ===== M2: the pair-decomposition identity (compositional core) ===== *)
Fixpoint list_sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + list_sum t end.
Lemma list_sum_app : forall a b, list_sum (a ++ b) = list_sum a + list_sum b.
Proof. induction a; intro b; cbn [app list_sum]; [reflexivity| rewrite IHa; lia]. Qed.
Lemma list_sum_map_add : forall (A : Type) (f g : A -> nat) (L : list A),
  list_sum (map (fun a => f a + g a) L) = list_sum (map f L) + list_sum (map g L).
Proof. intros A f g L; induction L as [|a t IH]; cbn [map list_sum]; lia. Qed.
Lemma list_sum_map_filter : forall (A : Type) (P : A -> bool) (h : A -> nat) (L : list A),
  list_sum (map (fun a => if P a then h a else 0) L) = list_sum (map h (filter P L)).
Proof. intros A P h L; induction L as [|a t IH]; cbn [map filter list_sum]; [reflexivity|];
  destruct (P a); cbn [map list_sum]; rewrite IH; lia. Qed.

Fixpoint upairs (l : list nat) : list (nat * nat) :=
  match l with [] => [] | x :: t => map (fun y => (x, y)) t ++ upairs t end.

Lemma upairs_filter : forall (P : nat -> bool) l,
  upairs (filter P l) = filter (fun ab => P (fst ab) && P (snd ab)) (upairs l).
Proof.
  intros P l; induction l as [|x t IH]; cbn [filter upairs]; [reflexivity|].
  destruct (P x) eqn:Px; cbn [upairs].
  - rewrite filter_app, IH. f_equal. clear IH.
    induction t as [|y s IHt]; cbn [map filter]; [reflexivity|].
    destruct (P y) eqn:Py; cbn [map filter fst snd]; rewrite Px; cbn.
    + rewrite Py. cbn. rewrite IHt. reflexivity.
    + rewrite Py. cbn. exact IHt.
  - rewrite IH. clear IH. rewrite filter_app.
    replace (filter (fun ab => P (fst ab) && P (snd ab)) (map (fun y => (x, y)) t)) with (@nil (nat*nat)).
    + reflexivity.
    + induction t as [|y s IHt]; cbn [map filter fst snd]; [reflexivity|].
      rewrite Px; cbn. exact IHt.
Qed.

Lemma in_upairs : forall l a b, In (a,b) (upairs l) -> In a l /\ In b l.
Proof.
  induction l as [|x t IH]; intros a b H; cbn [upairs] in H; [contradiction|].
  apply in_app_or in H as [H|H].
  - apply in_map_iff in H as [y [Heq Hy]]. inversion Heq; subst. split; [left; reflexivity| right; exact Hy].
  - apply IH in H as [Ha Hb]. split; right; assumption.
Qed.

(* ---- interval predicate and the "compared" indicator over the program input ---- *)
Definition betw (a b x : nat) : bool := (Nat.min a b <=? x) && (x <=? Nat.max a b).
Definition comparedb (a b : nat) (l : list nat) : bool :=
  match filter (betw a b) l with [] => false | x :: _ => (x =? a) || (x =? b) end.
Definition ind (l : list nat) (ab : nat * nat) : nat :=
  if comparedb (fst ab) (snd ab) l then 1 else 0.
Definition pairsum (l : list nat) : nat := list_sum (map (ind l) (upairs l)).

Lemma filter_subset : forall (Q R : nat -> bool) l,
  (forall x, Q x = true -> R x = true) -> filter Q (filter R l) = filter Q l.
Proof.
  intros Q R l Hsub; induction l as [|x t IH]; cbn [filter]; [reflexivity|].
  destruct (R x) eqn:Rx.
  - cbn [filter]. destruct (Q x); rewrite IH; reflexivity.
  - destruct (Q x) eqn:Qx; [rewrite (Hsub x Qx) in Rx; discriminate| exact IH].
Qed.

Lemma betw_out_high : forall a b p, a < p -> b < p -> betw a b p = false.
Proof. intros a b p Ha Hb. unfold betw. apply andb_false_iff. right.
  apply Nat.leb_gt. apply Nat.max_lub_lt; assumption. Qed.
Lemma betw_out_low : forall a b p, p < a -> p < b -> betw a b p = false.
Proof. intros a b p Ha Hb. unfold betw. apply andb_false_iff. left.
  apply Nat.leb_gt. apply Nat.min_glb_lt; assumption. Qed.
Lemma betw_lt : forall a b p x, a < p -> b < p -> betw a b x = true -> x <? p = true.
Proof. intros a b p x Ha Hb Hbw. unfold betw in Hbw. apply andb_true_iff in Hbw as [_ H2].
  apply Nat.leb_le in H2. apply Nat.ltb_lt. assert (Nat.max a b < p) by (apply Nat.max_lub_lt; assumption). lia. Qed.
Lemma betw_gt : forall a b p x, p < a -> p < b -> betw a b x = true -> p <? x = true.
Proof. intros a b p x Ha Hb Hbw. unfold betw in Hbw. apply andb_true_iff in Hbw as [H1 _].
  apply Nat.leb_le in H1. apply Nat.ltb_lt. assert (p < Nat.min a b) by (apply Nat.min_glb_lt; assumption). lia. Qed.
Lemma betw_straddle1 : forall a b p, a < p -> p < b -> betw a b p = true.
Proof. intros a b p Ha Hb. unfold betw. apply andb_true_iff. split; [apply Nat.leb_le|apply Nat.leb_le].
  - assert (Nat.min a b <= a) by apply Nat.le_min_l. lia.
  - assert (b <= Nat.max a b) by apply Nat.le_max_r. lia. Qed.
Lemma betw_straddle2 : forall a b p, b < p -> p < a -> betw a b p = true.
Proof. intros a b p Ha Hb. unfold betw. apply andb_true_iff. split; [apply Nat.leb_le|apply Nat.leb_le].
  - assert (Nat.min a b <= b) by apply Nat.le_min_r. lia.
  - assert (a <= Nat.max a b) by apply Nat.le_max_l. lia. Qed.

Lemma comparedb_drop_head : forall a b p xs, betw a b p = false -> comparedb a b (p::xs) = comparedb a b xs.
Proof. intros a b p xs H. unfold comparedb. cbn [filter]. rewrite H. reflexivity. Qed.
Lemma comparedb_head_pivot : forall a b p xs, betw a b p = true -> a <> p -> b <> p -> comparedb a b (p::xs) = false.
Proof. intros a b p xs H Ha Hb. unfold comparedb. cbn [filter]. rewrite H.
  apply orb_false_iff. split; apply Nat.eqb_neq; auto. Qed.
Lemma comparedb_filter_eq : forall a b (R : nat -> bool) xs,
  (forall x, betw a b x = true -> R x = true) -> comparedb a b (filter R xs) = comparedb a b xs.
Proof. intros a b R xs Hsub. unfold comparedb. rewrite filter_subset by exact Hsub. reflexivity. Qed.

(* the crux: one pair's contribution splits across the two partitions *)
Lemma ind_pivot : forall p a b xs, a <> p -> b <> p ->
  ind (p::xs) (a,b)
  = (if (a <? p) && (b <? p) then ind (filter (fun x => x <? p) xs) (a,b) else 0)
  + (if (p <? a) && (p <? b) then ind (filter (fun x => p <? x) xs) (a,b) else 0).
Proof.
  intros p a b xs Ha Hb. unfold ind; cbn [fst snd].
  destruct (lt_eq_lt_dec a p) as [[Hap|Hap]|Hap]; [|exfalso; auto|];
  destruct (lt_eq_lt_dec b p) as [[Hbp|Hbp]|Hbp]; try (exfalso; auto; fail).
  - (* a<p, b<p *)
    rewrite (proj2 (Nat.ltb_lt a p) Hap), (proj2 (Nat.ltb_lt b p) Hbp); cbn [andb].
    assert (Hpa : (p <? a) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hpa; cbn [andb]. rewrite Nat.add_0_r.
    rewrite (comparedb_drop_head a b p xs (betw_out_high a b p Hap Hbp)).
    rewrite (comparedb_filter_eq a b (fun x => x <? p) xs (fun x => betw_lt a b p x Hap Hbp)). reflexivity.
  - (* a<p, b>p : straddle *)
    rewrite (comparedb_head_pivot a b p xs (betw_straddle1 a b p Hap Hbp) Ha Hb).
    assert (Hbp' : (b <? p) = false) by (apply Nat.ltb_ge; lia).
    assert (Hpa : (p <? a) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hbp', Hpa, Bool.andb_false_r; cbn [andb]. reflexivity.
  - (* a>p, b<p : straddle *)
    rewrite (comparedb_head_pivot a b p xs (betw_straddle2 a b p Hbp Hap) Ha Hb).
    assert (Hap' : (a <? p) = false) by (apply Nat.ltb_ge; lia).
    assert (Hpb : (p <? b) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hap', Hpb; cbn [andb]. rewrite Bool.andb_false_r. reflexivity.
  - (* a>p, b>p *)
    rewrite (proj2 (Nat.ltb_lt p a) Hap), (proj2 (Nat.ltb_lt p b) Hbp); cbn [andb].
    assert (Hap' : (a <? p) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hap'; cbn [andb].
    rewrite (comparedb_drop_head a b p xs (betw_out_low a b p Hap Hbp)).
    rewrite (comparedb_filter_eq a b (fun x => p <? x) xs (fun x => betw_gt a b p x Hap Hbp)). reflexivity.
Qed.

Lemma list_sum_map_one : forall (A : Type) (l : list A), list_sum (map (fun _ => 1) l) = length l.
Proof. intros A l; induction l as [|x t IH]; cbn [map list_sum length]; lia. Qed.

Lemma NoDup_filter_nat : forall (P : nat -> bool) l, NoDup l -> NoDup (filter P l).
Proof.
  intros P l; induction l as [|x t IH]; intro Hnd; cbn [filter]; [constructor|].
  inversion Hnd as [|x' l' Hin Hnd']; subst.
  destruct (P x).
  - constructor; [|apply IH; exact Hnd']. intro Hc. apply Hin. apply filter_In in Hc as [Hc _]. exact Hc.
  - apply IH; exact Hnd'.
Qed.

Lemma pairsum_cons : forall p xs, NoDup (p :: xs) ->
  pairsum (p :: xs) = length xs + pairsum (filter (fun x => x <? p) xs)
                                + pairsum (filter (fun x => p <? x) xs).
Proof.
  intros p xs Hnd. inversion Hnd as [|p' xs' Hpin Hndxs]; subst.
  unfold pairsum at 1. cbn [upairs]. rewrite map_app, list_sum_app.
  (* Part 1: the pivot-pairs each contribute 1 *)
  rewrite map_map.
  assert (HP1 : map (fun y => ind (p :: xs) (p, y)) xs = map (fun _ => 1) xs).
  { apply map_ext_in. intros y _. unfold ind; cbn [fst snd]. unfold comparedb.
    cbn [filter]. unfold betw.
    rewrite (proj2 (Nat.leb_le _ _) (Nat.le_min_l p y)).
    rewrite (proj2 (Nat.leb_le _ _) (Nat.le_max_l p y)). cbn.
    rewrite Nat.eqb_refl. reflexivity. }
  rewrite HP1, list_sum_map_one.
  (* Part 2: the rest splits across the two partitions *)
  assert (HP2 : map (ind (p :: xs)) (upairs xs)
    = map (fun ab => (if (fst ab <? p) && (snd ab <? p)
                      then ind (filter (fun x => x <? p) xs) ab else 0)
                   + (if (p <? fst ab) && (p <? snd ab)
                      then ind (filter (fun x => p <? x) xs) ab else 0)) (upairs xs)).
  { apply map_ext_in. intros [a b] Hin. apply in_upairs in Hin as [Ha Hb].
    apply (ind_pivot p a b xs); intro Hc; subst; auto. }
  rewrite HP2, list_sum_map_add.
  rewrite (list_sum_map_filter _ (fun ab => (fst ab <? p) && (snd ab <? p)) (ind (filter (fun x => x <? p) xs))).
  rewrite (list_sum_map_filter _ (fun ab => (p <? fst ab) && (p <? snd ab)) (ind (filter (fun x => p <? x) xs))).
  rewrite <- (upairs_filter (fun x => x <? p) xs).
  rewrite <- (upairs_filter (fun x => p <? x) xs).
  unfold pairsum. lia.
Qed.

Theorem cmp_eq_pairsum_aux : forall n l, length l <= n -> NoDup l -> cmp l = pairsum l.
Proof.
  induction n as [|n IH]; intros l Hlen Hnd.
  - destruct l; cbn [length] in *; [|lia]. reflexivity.
  - destruct l as [|p xs]; [reflexivity|]. cbn [length] in Hlen.
    rewrite cmp_cons, (pairsum_cons p xs Hnd).
    inversion Hnd as [|p' xs' Hpin Hndxs]; subst.
    pose proof (filter_length_le (fun x => x <? p) xs) as Hlo.
    pose proof (filter_length_le (fun x => p <? x) xs) as Hhi.
    rewrite (IH (filter (fun x => x <? p) xs)) by (try lia; apply NoDup_filter_nat; exact Hndxs).
    rewrite (IH (filter (fun x => p <? x) xs)) by (try lia; apply NoDup_filter_nat; exact Hndxs).
    reflexivity.
Qed.

(* The pair-decomposition identity: the comparison count of head-pivot quicksort
   equals the number of element pairs that ever get directly compared. *)
Theorem cmp_eq_pairsum : forall l, NoDup l -> cmp l = pairsum l.
Proof. intros l. apply (cmp_eq_pairsum_aux (length l)). lia. Qed.


(* ---- computational tie to the closed form: sum cmp over all permutations ---- *)
Fixpoint inserts (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: t => (x :: y :: t) :: map (fun z => y :: z) (inserts x t)
  end.
Fixpoint perms (l : list nat) : list (list nat) :=
  match l with [] => [[]] | x :: t => flat_map (inserts x) (perms t) end.
Definition Tot (n : nat) : nat := list_sum (map cmp (perms (seq 0 n))).

(* Tot n = (enumerated mean) * n!; matches tools/conjecture/results/quicksort-average.json
   small_values 0,0,1,8/3,29/6,37/5,103/10 times n!. The real instrumented program,
   summed over every permutation, reproduces the closed form's small values. *)
Example Tot_2 : Tot 2 = 2.    Proof. vm_compute. reflexivity. Qed.
Example Tot_3 : Tot 3 = 16.   Proof. vm_compute. reflexivity. Qed.
Example Tot_4 : Tot 4 = 116.  Proof. vm_compute. reflexivity. Qed.
Example Tot_5 : Tot 5 = 888.  Proof. vm_compute. reflexivity. Qed.
Example Tot_6 : Tot 6 = 7416. Proof. vm_compute. reflexivity. Qed.

(* ---- Stage 2, Part B (combinatorial count), checked computationally for small n ----
   A value-pair {a,b} at interval distance d = b-a+1 is "compared" iff, among the d
   values in [a,b], the first to appear in the permutation is a or b. Over all n!
   permutations each of the d interval-values is equally likely to come first, so a
   fixed pair is compared in exactly 2*n!/d of them. Hence
     Tot n = Sum_{a<b} 2*n!/(b-a+1) = 2*n! * Sum_{d=2}^{n} (n+1-d)/d
   and QuicksortPairSum.v proves 2 * Sum_{d=2}^{n}(n+1-d)/d = 2(n+1)H_n - 4n.
   The general count (= 2*n!/d) is the one remaining lemma (Part B); here it and the
   regrouping Tot = Sum_{pairs} count are verified for small n by vm_compute. *)
Definition num_compared (a b n : nat) : nat :=
  length (filter (fun s => comparedb a b s) (perms (seq 0 n))).

Example cnt_4_d2 : num_compared 0 1 4 = 24.  Proof. vm_compute. reflexivity. Qed.  (* 2*4!/2 *)
Example cnt_4_d3 : num_compared 0 2 4 = 16.  Proof. vm_compute. reflexivity. Qed.  (* 2*4!/3 *)
Example cnt_4_d4 : num_compared 0 3 4 = 12.  Proof. vm_compute. reflexivity. Qed.  (* 2*4!/4 *)
Example cnt_5_d2 : num_compared 0 1 5 = 120. Proof. vm_compute. reflexivity. Qed.  (* 2*5!/2 *)
Example cnt_5_d5 : num_compared 0 4 5 = 48.  Proof. vm_compute. reflexivity. Qed.  (* 2*5!/5 *)

Definition Totpairs (n : nat) : nat :=
  list_sum (map (fun ab => num_compared (fst ab) (snd ab) n) (upairs (seq 0 n))).
Example Totpairs_4 : Totpairs 4 = Tot 4. Proof. vm_compute. reflexivity. Qed.
Example Totpairs_5 : Totpairs 5 = Tot 5. Proof. vm_compute. reflexivity. Qed.
Example Totpairs_6 : Totpairs 6 = Tot 6. Proof. vm_compute. reflexivity. Qed.

Print Assumptions cmp_eq_pairsum.
