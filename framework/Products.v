(* analysis@home framework: product-space (assignment) enumeration (axiom-free).
 *
 * The permutation analogue is framework/Permutations.v. This is its product
 * counterpart for average-case cost over INDEPENDENT coordinates -- e.g. hashing
 * n keys into n slots, the space {1..n}^k. Self-contained (stdlib only).
 *
 *   prods n k          : every length-k assignment with entries in {1..n}
 *   length_prods       : length (prods n k) = n^k
 *   sum_count_eq_length: SUM over v in {1..n} of (multiplicity of v in c) = |c|
 *                        -- the product "marginalization" primitive: summing a
 *                        per-slot indicator over all slots collapses to the running
 *                        count (the analogue of count_first uniformity). It is what
 *                        turns a pairwise expectation into a running-multiplicity
 *                        recurrence (see work-units/collisions-expected-hashing).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)
Require Import List Arith Lia.
Import ListNotations.

Fixpoint list_sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + list_sum t end.
Lemma list_sum_app : forall a b, list_sum (a ++ b) = list_sum a + list_sum b.
Proof. induction a as [|x t IH]; intro b; cbn [app list_sum]; [reflexivity| rewrite IH; lia]. Qed.
Lemma list_sum_flat_map : forall A (H : A -> list nat) L,
  list_sum (flat_map H L) = list_sum (map (fun x => list_sum (H x)) L).
Proof. intros A H L; induction L as [|x t IH]; cbn [flat_map map list_sum];
  [reflexivity| rewrite list_sum_app, IH; reflexivity]. Qed.
Lemma map_flat_map : forall A B C (f : B -> C) (g : A -> list B) L,
  map f (flat_map g L) = flat_map (fun x => map f (g x)) L.
Proof. intros A B C f g L; induction L as [|x t IH]; cbn [flat_map map];
  [reflexivity| rewrite map_app, IH; reflexivity]. Qed.
Lemma len_flat_map : forall A B (H : A -> list B) L,
  length (flat_map H L) = list_sum (map (fun x => length (H x)) L).
Proof. intros A B H L; induction L as [|x t IH]; cbn [flat_map map list_sum];
  [reflexivity| rewrite app_length, IH; reflexivity]. Qed.
Lemma list_sum_map_add : forall A (f g : A -> nat) l,
  list_sum (map (fun a => f a + g a) l) = list_sum (map f l) + list_sum (map g l).
Proof. intros A f g l; induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.
Lemma list_sum_map_scale_l : forall A (f : A -> nat) c l,
  list_sum (map (fun a => c * f a) l) = c * list_sum (map f l).
Proof. intros A f c l; induction l as [|x t IH]; cbn [map list_sum]; lia. Qed.
Lemma list_sum_map_const : forall A c (l : list A), list_sum (map (fun _ => c) l) = c * length l.
Proof. intros A c l; induction l as [|x t IH]; cbn [map list_sum length]; lia. Qed.
Lemma count_absent : forall v l, (forall k, In k l -> v =? k = false) ->
  list_sum (map (fun k => if v =? k then 1 else 0) l) = 0.
Proof. intros v l H; induction l as [|x t IH]; cbn [map list_sum]; [reflexivity|].
  rewrite (H x) by (left; reflexivity). rewrite IH; [reflexivity| intros k Hk; apply H; right; exact Hk]. Qed.
Lemma count_hit : forall x a m, a <= x < a + m ->
  list_sum (map (fun v => if x =? v then 1 else 0) (seq a m)) = 1.
Proof.
  intros x a m. revert a. induction m as [|m IH]; intros a H; [lia|].
  cbn [seq map list_sum]. destruct (x =? a) eqn:E.
  - apply Nat.eqb_eq in E; subst a. rewrite count_absent.
    + reflexivity.
    + intros k Hk. apply in_seq in Hk. apply Nat.eqb_neq. lia.
  - apply Nat.eqb_neq in E. rewrite (IH (S a)) by lia. reflexivity.
Qed.

Fixpoint count_eq (v : nat) (c : list nat) : nat :=
  match c with [] => 0 | x :: t => (if x =? v then 1 else 0) + count_eq v t end.
Lemma count_eq_app : forall v c w, count_eq v (c ++ [w]) = count_eq v c + (if w =? v then 1 else 0).
Proof. intros v c w; induction c as [|x t IH]; cbn [app count_eq]; [lia| rewrite IH; lia]. Qed.
Lemma sum_count_eq_length : forall n c, (forall x, In x c -> 1 <= x <= n) ->
  list_sum (map (fun v => count_eq v c) (seq 1 n)) = length c.
Proof.
  intros n c. induction c as [|x t IH]; intro Hr.
  - cbn [count_eq length]. rewrite list_sum_map_const. lia.
  - cbn [count_eq length]. rewrite list_sum_map_add.
    rewrite (count_hit x 1 n) by (pose proof (Hr x (or_introl eq_refl)); lia).
    rewrite IH by (intros y Hy; apply Hr; right; exact Hy). lia.
Qed.

Fixpoint prods (n k : nat) : list (list nat) :=
  match k with
  | 0 => [ [] ]
  | S m => flat_map (fun c => map (fun v => c ++ [v]) (seq 1 n)) (prods n m)
  end.
Lemma in_prods_length : forall n k c, In c (prods n k) -> length c = k.
Proof.
  induction k as [|m IH]; intros c Hc; cbn [prods] in Hc.
  - destruct Hc as [<-|[]]. reflexivity.
  - apply in_flat_map in Hc as [c0 [Hc0 Hin]]. apply in_map_iff in Hin as [v [<- _]].
    rewrite app_length; cbn [length]. rewrite (IH c0 Hc0). lia.
Qed.
Lemma in_prods_range : forall n k c, In c (prods n k) -> forall x, In x c -> 1 <= x <= n.
Proof.
  induction k as [|m IH]; intros c Hc x Hx; cbn [prods] in Hc.
  - destruct Hc as [<-|[]]. destruct Hx.
  - apply in_flat_map in Hc as [c0 [Hc0 Hin]]. apply in_map_iff in Hin as [v [<- Hv]].
    apply in_app_or in Hx as [Hx|Hx].
    + exact (IH c0 Hc0 x Hx).
    + cbn in Hx. destruct Hx as [<-|[]]. apply in_seq in Hv. lia.
Qed.
Lemma length_prods : forall n k, length (prods n k) = n ^ k.
Proof.
  induction k as [|m IH]; [reflexivity|]. cbn [prods Nat.pow]. rewrite len_flat_map.
  assert (E : map (fun c => length (map (fun v => c ++ [v]) (seq 1 n))) (prods n m)
            = map (fun _ => n) (prods n m)).
  { apply map_ext. intro c. rewrite map_length, seq_length. reflexivity. }
  rewrite E, list_sum_map_const, IH. reflexivity.
Qed.

Print Assumptions length_prods.
Print Assumptions sum_count_eq_length.
