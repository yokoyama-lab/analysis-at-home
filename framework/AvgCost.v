(* analysis@home — average-case cost framework (seed).
 *
 * The pivot from a pile of ad-hoc average-case lemmas to a REUSABLE discipline:
 * an algorithm is instrumented with an operation counter, the input distribution
 * is a finite (here: uniform) family of inputs, and the EXPECTED cost is a first
 * class object. The proof obligation is kept division-free:
 *
 *   mean_eq costs p q  :=  q * Σcosts = p * |costs|      ("E[cost] = p/q")
 *
 * `costs` is the list of per-outcome operation counts of the instrumented
 * algorithm over the (uniform) family of inputs; mean_eq says their average is
 * exactly p/q. (A rational-valued `expect : list nat -> Q` wrapper with
 * `mean_eq costs p q -> expect costs == p#q` is a thin one-time QArith lemma.)
 *
 * The conjecture track (tools/conjecture/) computes the same E[cost] by exhaustive
 * enumeration; it is a property-based ORACLE that the formal statement is faithful
 * BEFORE it is proved (compute -> test the spec -> prove).
 *
 * First instance: linear search for a uniformly random present target —
 * E[comparisons] = (n+1)/2 — derived through the framework's `mean_eq`, grounded
 * in the instrumented counter `lc` (not a closed-form re-statement).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint list_sum (l : list nat) : nat :=
  match l with [] => 0 | x :: t => x + list_sum t end.

(* framework primitive: the average of the per-outcome costs is exactly p/q *)
Definition mean_eq (costs : list nat) (p q : nat) : Prop :=
  q * list_sum costs = p * length costs.

(* instrumented linear search: the number of comparisons to find `key` *)
Fixpoint lc (key : nat) (l : list nat) : nat :=
  match l with [] => 0 | x :: t => if x =? key then 1 else S (lc key t) end.

(* cost grounding: searching seq a m for a present key costs (k - a + 1) *)
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
  induction n as [|n IH]; [reflexivity|].
  rewrite seq_S, list_sum_app. nia.
Qed.

(* E[comparisons] of linear search for a uniformly random present target = (n+1)/2 *)
Theorem linear_search_avg :
  forall n, mean_eq (map (fun k => lc k (seq 1 n)) (seq 1 n)) (n + 1) 2.
Proof.
  intro n. unfold mean_eq.
  rewrite length_map, length_seq.
  assert (Hmap : map (fun k => lc k (seq 1 n)) (seq 1 n) = seq 1 n).
  { transitivity (map (fun k => k) (seq 1 n)).
    - apply map_ext_in. intros k Hk. apply in_seq in Hk.
      rewrite (lc_seq n 1 k) by lia. lia.
    - induction (seq 1 n) as [|a t IHt]; [reflexivity|].
      cbn [map]. rewrite IHt. reflexivity. }
  rewrite Hmap, sum_seq1. lia.
Qed.
