(* analysis@home -- work unit: collisions-expected-hashing (Rocq target, FRAMEWORK REUSE).
 *
 * Companion to Coll.v (which is self-contained). This file proves the SAME result
 * -- E[#collisions of n keys in n slots] = (n-1)/2 -- but by REUSING the shared
 * product-space library framework/Products.v (Require Import Products): the
 * assignment generator prods, length_prods (= n^k), and the marginalization
 * primitive sum_count_eq_length (SUM over slots of a multiplicity = |c|), which is
 * exactly what collapses the pairwise collision sum to the running-multiplicity
 * recurrence Tot_coll(S m) = n*Tot_coll m + m*n^m. Only the collision-specific
 * counter coll and the assembly live here; the product enumeration is the library.
 *
 * This is the product-space analogue of records' reuse of framework/Permutations.v
 * (count_first_value): the framework now carries BOTH a permutation library and a
 * product library for average-case cost.
 *
 * VERIFIED (Print Assumptions collisions_expected_reuse: closed under the global context). *)

Require Import List Arith Lia.
Require Import Products.
Import ListNotations.

(* coll counts colliding (key) pairs of an assignment: positions i<j with c_i=c_j. *)
Fixpoint coll (c : list nat) : nat :=
  match c with [] => 0 | x :: t => coll t + count_eq x t end.
Lemma coll_app : forall c w, coll (c ++ [w]) = coll c + count_eq w c.
Proof.
  induction c as [|x t IH]; intro w; cbn [app coll].
  - cbn [count_eq]. lia.
  - rewrite IH, count_eq_app. cbn [count_eq].
    replace (w =? x) with (x =? w) by (apply Nat.eqb_sym). lia.
Qed.

Definition Tot_coll (n k : nat) : nat := list_sum (map coll (prods n k)).

(* recurrence: REUSES the framework's sum_count_eq_length and length_prods *)
Lemma Tot_coll_rec : forall n m, Tot_coll n (S m) = n * Tot_coll n m + m * n ^ m.
Proof.
  intros n m. unfold Tot_coll. cbn [prods]. rewrite map_flat_map, list_sum_flat_map.
  assert (E : map (fun c => list_sum (map coll (map (fun v => c ++ [v]) (seq 1 n)))) (prods n m)
            = map (fun c => n * coll c + m) (prods n m)).
  { apply map_ext_in. intros c Hc. rewrite map_map.
    assert (E2 : map (fun v => coll (c ++ [v])) (seq 1 n)
               = map (fun v => coll c + count_eq v c) (seq 1 n)).
    { apply map_ext_in. intros v _. rewrite coll_app. reflexivity. }
    rewrite E2, list_sum_map_add, list_sum_map_const, seq_length.
    rewrite (sum_count_eq_length n c) by (apply (in_prods_range n m c Hc)).
    rewrite (in_prods_length n m c Hc), Nat.mul_comm. reflexivity. }
  rewrite E, list_sum_map_add, list_sum_map_scale_l, (list_sum_map_const _ m), length_prods.
  fold (Tot_coll n m). reflexivity.
Qed.

Lemma Tot_coll_key : forall n k, 2 * n * Tot_coll n k + k * n ^ k = k * k * n ^ k.
Proof.
  intros n k. induction k as [|m IH].
  - unfold Tot_coll; cbn [prods map coll list_sum Nat.pow]; lia.
  - rewrite Tot_coll_rec. cbn [Nat.pow].
    pose proof (f_equal (Nat.mul n) IH) as HnIH. nia.
Qed.

(* E[#collisions] of n keys into n slots (load 1) is (n-1)/2, division-free.
   Same statement as Coll.v's collisions_expected, but PROVED BY REUSING the
   product-space library framework/Products.v. *)
Theorem collisions_expected_reuse : forall n, (0 < n)%nat -> 2 * Tot_coll n n = (n - 1) * n ^ n.
Proof.
  intros n Hn. pose proof (Tot_coll_key n n) as K.
  apply (Nat.mul_cancel_l _ _ n); [lia|]. nia.
Qed.

Print Assumptions collisions_expected_reuse.
