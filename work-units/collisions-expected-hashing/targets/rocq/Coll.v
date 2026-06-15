(* analysis@home — work unit: collisions-expected-hashing (Rocq target).
 *
 * SECOND DEEP AVERAGE-CASE RESULT, with a different (pairwise) structure from
 * records. Throwing n keys into n slots (load 1), the expected number of
 * colliding pairs is (n-1)/2 — the verified twin of the enumerated
 * hashing-collisions.json. Stated division-free (E = p/q as q*Σ = p*|.|):
 *   collisions_expected : 0 < n -> 2 * Tot_coll n n = (n-1) * n^n.
 *
 * As with records we do NOT enumerate the n^n assignments. The assignment space
 * is the product {1..n}^k; appending the k-th key (uniform in {1..n}) adds
 * count_eq v c new collisions, and Σ_{v∈{1..n}} count_eq v c = |c| (each existing
 * key matched once). This gives Tot_coll(S m) = n*Tot_coll m + m*n^m, hence the
 * subtraction-free identity 2*n*Tot_coll n k + k*n^k = k*k*n^k (= C(k,2)/n), and
 * at k=n the load-1 mean (n-1)/2. (Linearity over the last coordinate again —
 * the pairwise sum collapses to the running multiplicity.)
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

(* exactly one v in [a, a+m) equals x *)
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

(* ---- multiplicity and collision counters ---- *)
Fixpoint count_eq (v : nat) (c : list nat) : nat :=
  match c with [] => 0 | x :: t => (if x =? v then 1 else 0) + count_eq v t end.
Fixpoint coll (c : list nat) : nat :=
  match c with [] => 0 | x :: t => coll t + count_eq x t end.

Lemma count_eq_app : forall v c w, count_eq v (c ++ [w]) = count_eq v c + (if w =? v then 1 else 0).
Proof. intros v c w; induction c as [|x t IH]; cbn [app count_eq]; [lia| rewrite IH; lia]. Qed.

Lemma coll_app : forall c w, coll (c ++ [w]) = coll c + count_eq w c.
Proof.
  induction c as [|x t IH]; intro w; cbn [app coll].
  - cbn [count_eq]. lia.
  - rewrite IH, count_eq_app. cbn [count_eq].
    replace (w =? x) with (x =? w) by (apply Nat.eqb_sym). lia.
Qed.

(* Σ_{v∈{1..n}} count_eq v c = |c|, when all entries of c are in {1..n} *)
Lemma sum_count_eq_length : forall n c, (forall x, In x c -> 1 <= x <= n) ->
  list_sum (map (fun v => count_eq v c) (seq 1 n)) = length c.
Proof.
  intros n c. induction c as [|x t IH]; intro Hr.
  - cbn [count_eq length]. rewrite list_sum_map_const. lia.
  - cbn [count_eq length]. rewrite list_sum_map_add.
    rewrite (count_hit x 1 n) by (pose proof (Hr x (or_introl eq_refl)); lia).
    rewrite IH by (intros y Hy; apply Hr; right; exact Hy). lia.
Qed.

(* ---- assignment space: k keys into n slots; |assign n k| = n^k ---- *)
Fixpoint assign (n k : nat) : list (list nat) :=
  match k with
  | 0 => [ [] ]
  | S m => flat_map (fun c => map (fun v => c ++ [v]) (seq 1 n)) (assign n m)
  end.

Lemma in_assign_length : forall n k c, In c (assign n k) -> length c = k.
Proof.
  induction k as [|m IH]; intros c Hc; cbn [assign] in Hc.
  - destruct Hc as [<-|[]]. reflexivity.
  - apply in_flat_map in Hc as [c0 [Hc0 Hin]]. apply in_map_iff in Hin as [v [<- _]].
    rewrite app_length; cbn [length]. rewrite (IH c0 Hc0). lia.
Qed.

Lemma in_assign_range : forall n k c, In c (assign n k) -> forall x, In x c -> 1 <= x <= n.
Proof.
  induction k as [|m IH]; intros c Hc x Hx; cbn [assign] in Hc.
  - destruct Hc as [<-|[]]. destruct Hx.
  - apply in_flat_map in Hc as [c0 [Hc0 Hin]]. apply in_map_iff in Hin as [v [<- Hv]].
    apply in_app_or in Hx as [Hx|Hx].
    + exact (IH c0 Hc0 x Hx).
    + cbn in Hx. destruct Hx as [<-|[]]. apply in_seq in Hv. lia.
Qed.

Lemma length_assign : forall n k, length (assign n k) = n ^ k.
Proof.
  induction k as [|m IH]; [reflexivity|]. cbn [assign Nat.pow]. rewrite len_flat_map.
  assert (E : map (fun c => length (map (fun v => c ++ [v]) (seq 1 n))) (assign n m)
            = map (fun _ => n) (assign n m)).
  { apply map_ext. intro c. rewrite map_length, seq_length. reflexivity. }
  rewrite E, list_sum_map_const, IH. reflexivity.
Qed.

Definition Tot_coll (n k : nat) : nat := list_sum (map coll (assign n k)).

Lemma Tot_coll_rec : forall n m, Tot_coll n (S m) = n * Tot_coll n m + m * n ^ m.
Proof.
  intros n m. unfold Tot_coll. cbn [assign]. rewrite map_flat_map, list_sum_flat_map.
  assert (E : map (fun c => list_sum (map coll (map (fun v => c ++ [v]) (seq 1 n)))) (assign n m)
            = map (fun c => n * coll c + m) (assign n m)).
  { apply map_ext_in. intros c Hc. rewrite map_map.
    assert (E2 : map (fun v => coll (c ++ [v])) (seq 1 n)
               = map (fun v => coll c + count_eq v c) (seq 1 n)).
    { apply map_ext_in. intros v _. rewrite coll_app. reflexivity. }
    rewrite E2, list_sum_map_add, list_sum_map_const, seq_length.
    rewrite (sum_count_eq_length n c) by (apply (in_assign_range n m c Hc)).
    rewrite (in_assign_length n m c Hc), Nat.mul_comm. reflexivity. }
  rewrite E, list_sum_map_add, list_sum_map_scale_l, (list_sum_map_const _ m), length_assign.
  fold (Tot_coll n m). reflexivity.
Qed.

(* division-free (subtraction-free): 2*n*Tot_coll n k + k*n^k = k*k*n^k,
   i.e. E[#collisions over k keys, n slots] = k*(k-1)/(2n) = C(k,2)/n *)
Lemma Tot_coll_key : forall n k, 2 * n * Tot_coll n k + k * n ^ k = k * k * n ^ k.
Proof.
  intros n k. induction k as [|m IH].
  - unfold Tot_coll; cbn [assign map coll list_sum Nat.pow]; lia.
  - rewrite Tot_coll_rec. cbn [Nat.pow].
    pose proof (f_equal (Nat.mul n) IH) as HnIH. nia.
Qed.

(* E[#collisions] of n keys into n slots (load 1) is (n-1)/2, division-free *)
Theorem collisions_expected : forall n, (0 < n)%nat -> 2 * Tot_coll n n = (n - 1) * n ^ n.
Proof.
  intros n Hn. pose proof (Tot_coll_key n n) as K.
  apply (Nat.mul_cancel_l _ _ n); [lia|]. nia.
Qed.
