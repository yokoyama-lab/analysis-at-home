(* analysis@home — work unit: insertion-sort-comparisons-while (Rocq target)
 *
 * Cost model: while-ops / counts = ["key-comparison"].
 *
 * This is the SAME claim as the functional unit insertion-sort-comparisons,
 * but stated over a small imperative WHILE language with a big-step,
 * cost-annotated operational semantics. The counted operation is the *key
 * comparison* between an array element and the held key (the [BKLe] form);
 * index/bookkeeping tests ([BLe]) are free, matching how analysis of
 * algorithms counts a single dominant operation.
 *
 * VERIFIED. The semantics and the [insertion_sort] program are fixed; the
 * worst-case key-comparison bound is proved (no Admitted/Axiom — checked with
 * `Print Assumptions`: closed under the global context). CI compiles this
 * file. The lean/agda/isabelle targets remain open work units. *)

Require Import List Arith Lia.
Import ListNotations.

(* ---------- State: a mutable array + scalar variables ---------- *)

Definition vstore := nat -> nat.
Record state := mk_state { arr : list nat; vars : vstore }.

Definition upd (s : vstore) (x v : nat) : vstore :=
  fun y => if Nat.eqb x y then v else s y.

(* Write v at position i of l (no-op if i is out of range). *)
Fixpoint list_set (l : list nat) (i v : nat) : list nat :=
  match l, i with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S i' => h :: list_set t i' v
  end.

(* ---------- Arithmetic expressions (cost-free to evaluate) ---------- *)

Inductive aexp : Type :=
| ANum   (n : nat)
| AVar   (x : nat)
| AArr   (i : aexp)        (* arr[i] *)
| ALen                     (* length arr *)
| APlus  (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult  (a1 a2 : aexp).

Fixpoint aeval (s : state) (a : aexp) : nat :=
  match a with
  | ANum n     => n
  | AVar x     => vars s x
  | AArr i     => nth (aeval s i) (arr s) 0
  | ALen       => length (arr s)
  | APlus  a b => aeval s a + aeval s b
  | AMinus a b => aeval s a - aeval s b
  | AMult  a b => aeval s a * aeval s b
  end.

(* ---------- Boolean expressions; [beval] returns (value, #key-comparisons) ---------- *)

Inductive bexp : Type :=
| BTrue
| BFalse
| BLe  (a1 a2 : aexp)   (* bookkeeping comparison: cost 0 *)
| BKLe (a1 a2 : aexp)   (* KEY comparison: the counted operation, cost 1 *)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Fixpoint beval (s : state) (b : bexp) : bool * nat :=
  match b with
  | BTrue      => (true, 0)
  | BFalse     => (false, 0)
  | BLe  a1 a2 => (Nat.leb (aeval s a1) (aeval s a2), 0)
  | BKLe a1 a2 => (Nat.leb (aeval s a1) (aeval s a2), 1)
  | BNot b1 =>
      let (v, c) := beval s b1 in (negb v, c)
  | BAnd b1 b2 =>
      let (v1, c1) := beval s b1 in
      if v1
      then let (v2, c2) := beval s b2 in (v2, c1 + c2)
      else (false, c1)   (* short-circuit: b2 not evaluated *)
  end.

(* ---------- Commands ---------- *)

Inductive com : Type :=
| CSkip
| CAss    (x : nat) (a : aexp)
| CArrAss (i : aexp) (a : aexp)   (* arr[i] := a *)
| CSeq    (c1 c2 : com)
| CIf     (b : bexp) (c1 c2 : com)
| CWhile  (b : bexp) (c : com).

(* ---------- Big-step, cost-annotated semantics ----------
   [ceval c s s' k] : running [c] from state [s] terminates in state [s']
   having performed [k] key comparisons. *)

Inductive ceval : com -> state -> state -> nat -> Prop :=
| E_Skip : forall s,
    ceval CSkip s s 0
| E_Ass : forall s x a,
    ceval (CAss x a) s (mk_state (arr s) (upd (vars s) x (aeval s a))) 0
| E_ArrAss : forall s i a,
    ceval (CArrAss i a) s
          (mk_state (list_set (arr s) (aeval s i) (aeval s a)) (vars s)) 0
| E_Seq : forall c1 c2 s s1 s2 k1 k2,
    ceval c1 s s1 k1 ->
    ceval c2 s1 s2 k2 ->
    ceval (CSeq c1 c2) s s2 (k1 + k2)
| E_IfTrue : forall b c1 c2 s s' kb k,
    beval s b = (true, kb) ->
    ceval c1 s s' k ->
    ceval (CIf b c1 c2) s s' (kb + k)
| E_IfFalse : forall b c1 c2 s s' kb k,
    beval s b = (false, kb) ->
    ceval c2 s s' k ->
    ceval (CIf b c1 c2) s s' (kb + k)
| E_WhileFalse : forall b c s kb,
    beval s b = (false, kb) ->
    ceval (CWhile b c) s s kb
| E_WhileTrue : forall b c s s1 s2 kb k1 k2,
    beval s b = (true, kb) ->
    ceval c s s1 k1 ->
    ceval (CWhile b c) s1 s2 k2 ->
    ceval (CWhile b c) s s2 (kb + k1 + k2).

(* ---------- Insertion sort in WHILE ----------
   Variables: vi = i, vj = j, vkey = key.

     i := 1;
     while i + 1 <= len:                       (* i < n ; bookkeeping *)
       key := arr[i];
       j := i;
       while (1 <= j) && not (arr[j-1] <= key): (* arr[j-1] > key ; KEY compare *)
         arr[j] := arr[j-1];
         j := j - 1;
       arr[j] := key;
       i := i + 1
*)

Definition vi   : nat := 0.
Definition vj   : nat := 1.
Definition vkey : nat := 2.

Definition inner_guard : bexp :=
  BAnd (BLe (ANum 1) (AVar vj))
       (BNot (BKLe (AArr (AMinus (AVar vj) (ANum 1))) (AVar vkey))).

Definition inner_body : com :=
  CSeq (CArrAss (AVar vj) (AArr (AMinus (AVar vj) (ANum 1))))
       (CAss vj (AMinus (AVar vj) (ANum 1))).

Definition outer_guard : bexp := BLe (APlus (AVar vi) (ANum 1)) ALen.

Definition outer_body : com :=
  CSeq (CAss vkey (AArr (AVar vi)))
  (CSeq (CAss vj (AVar vi))
  (CSeq (CWhile inner_guard inner_body)
  (CSeq (CArrAss (AVar vj) (AVar vkey))
        (CAss vi (APlus (AVar vi) (ANum 1)))))).

Definition insertion_sort : com :=
  CSeq (CAss vi (ANum 1)) (CWhile outer_guard outer_body).

Definition init (l : list nat) : state := mk_state l (fun _ => 0).

(* ====================== Proof ====================== *)

(* ---------- generic helpers ---------- *)

Lemma list_set_length : forall l i v, length (list_set l i v) = length l.
Proof.
  induction l as [|h t IH]; intros i v.
  - destruct i; reflexivity.
  - destruct i; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ceval_ass_inv : forall x a s s' k,
  ceval (CAss x a) s s' k ->
  s' = mk_state (arr s) (upd (vars s) x (aeval s a)) /\ k = 0.
Proof. intros. inversion H; subst. auto. Qed.

Lemma ceval_arrass_inv : forall i a s s' k,
  ceval (CArrAss i a) s s' k ->
  s' = mk_state (list_set (arr s) (aeval s i) (aeval s a)) (vars s) /\ k = 0.
Proof. intros. inversion H; subst. auto. Qed.

Lemma ceval_seq_inv : forall c1 c2 s s' k,
  ceval (CSeq c1 c2) s s' k ->
  exists s1 k1 k2, ceval c1 s s1 k1 /\ ceval c2 s1 s' k2 /\ k = k1 + k2.
Proof. intros. inversion H; subst. exists s1, k1, k2. auto. Qed.

Lemma ceval_arr_length : forall c s s' k,
  ceval c s s' k -> length (arr s') = length (arr s).
Proof.
  intros c s s' k H. induction H; simpl in *;
    try (rewrite list_set_length); lia.
Qed.

(* ---------- inner loop ---------- *)

Lemma inner_body_effect : forall s s1 k1,
  ceval inner_body s s1 k1 ->
  k1 = 0 /\ vars s1 vj = vars s vj - 1 /\ vars s1 vi = vars s vi /\ vars s1 vkey = vars s vkey.
Proof.
  intros s s1 k1 H. unfold inner_body in H.
  apply ceval_seq_inv in H. destruct H as [sm [km1 [km2 [Ha [Hb Hk]]]]].
  apply ceval_arrass_inv in Ha. destruct Ha as [Hsm Hk1].
  apply ceval_ass_inv in Hb. destruct Hb as [Hs1 Hk2].
  subst. unfold upd. simpl. repeat split; reflexivity.
Qed.

Lemma inner_loop_preserves : forall s s' k,
  ceval (CWhile inner_guard inner_body) s s' k ->
  vars s' vi = vars s vi /\ vars s' vkey = vars s vkey.
Proof.
  intros s s' k H. remember (CWhile inner_guard inner_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - inversion Hw; subst; split; reflexivity.
  - inversion Hw; subst b c. specialize (IHceval2 eq_refl).
    apply inner_body_effect in H0. destruct H0 as [_ [_ [Hvi Hvkey]]].
    destruct IHceval2 as [Hi Hk]. split.
    + rewrite Hi. exact Hvi.
    + rewrite Hk. exact Hvkey.
Qed.

(* Inserting the i-th element costs at most [vars s vj] key comparisons:
   the inner loop tests positions j = j0, j0-1, ..., 1, one comparison each. *)
Lemma inner_loop_bound : forall s s' k,
  ceval (CWhile inner_guard inner_body) s s' k -> k <= vars s vj.
Proof.
  intros s s' k H.
  remember (CWhile inner_guard inner_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - (* E_WhileFalse *)
    inversion Hw; subst b c; clear Hw.
    unfold inner_guard in H. simpl in H.
    remember (vars s vj) as jv eqn:Hjv.
    destruct jv as [|m]; simpl in H; inversion H; lia.
  - (* E_WhileTrue *)
    inversion Hw; subst b c.
    specialize (IHceval2 eq_refl).
    apply inner_body_effect in H0. destruct H0 as [Hk1 [Hvj _]].
    unfold inner_guard in H. simpl in H.
    remember (vars s vj) as jv eqn:Hjv.
    destruct jv as [|m]; simpl in H.
    + inversion H.
    + inversion H. rewrite Hvj in IHceval2. simpl in IHceval2. lia.
Qed.

(* ---------- outer loop ---------- *)

(* One outer iteration: cost <= i (inner_loop_bound with vj := i), it advances
   i, and it preserves the array length. *)
Lemma outer_body_effect : forall s s' k,
  ceval outer_body s s' k ->
  k <= vars s vi /\ vars s' vi = S (vars s vi) /\ length (arr s') = length (arr s).
Proof.
  intros s s' k H. unfold outer_body in H.
  apply ceval_seq_inv in H; destruct H as [s1 [ka [kb [HA [H1 Hk]]]]].
  apply ceval_ass_inv in HA; destruct HA as [Hs1 HkA].
  apply ceval_seq_inv in H1; destruct H1 as [s2 [kb1 [kb2 [HB [H2 Hk1]]]]].
  apply ceval_ass_inv in HB; destruct HB as [Hs2 HkB].
  apply ceval_seq_inv in H2; destruct H2 as [s3 [kc1 [kc2 [HW [H3 Hk2]]]]].
  apply ceval_seq_inv in H3; destruct H3 as [s4 [kd1 [kd2 [HC [HD Hk3]]]]].
  apply ceval_arrass_inv in HC; destruct HC as [Hs4 HkC].
  apply ceval_ass_inv in HD; destruct HD as [Hs' HkD].
  pose proof (inner_loop_bound _ _ _ HW) as Hib.
  pose proof (inner_loop_preserves _ _ _ HW) as Hip; destruct Hip as [Hpi _].
  pose proof (ceval_arr_length _ _ _ _ HW) as Hal.
  subst.
  unfold upd in *. simpl in *.
  repeat split.
  - lia.
  - rewrite Hpi. lia.
  - rewrite list_set_length. lia.
Qed.

(* Invariant (subtractive form, no precondition needed): from a state with
   vars vi = i and array length n, the outer loop performs k key comparisons
   with 2*k <= n*(n-1) - i*(i-1). For WhileFalse the RHS is a nat >= 0 so the
   bound is trivial; the work is the WhileTrue arithmetic. *)
Lemma outer_loop_bound : forall s s' k,
  ceval (CWhile outer_guard outer_body) s s' k ->
  2 * k <= length (arr s) * (length (arr s) - 1)
           - vars s vi * (vars s vi - 1).
Proof.
  intros s s' k H.
  remember (CWhile outer_guard outer_body) as w eqn:Hw.
  induction H; try discriminate Hw.
  - (* E_WhileFalse *)
    inversion Hw; subst b c; clear Hw.
    unfold outer_guard in H; simpl in H; injection H as Hval Hcost; subst kb.
    lia.
  - (* E_WhileTrue *)
    inversion Hw; subst b c.
    pose proof (outer_body_effect _ _ _ H0) as [Hk1 [Hvi Hlen]].
    unfold outer_guard in H; simpl in H; injection H as Hval Hcost; subst kb.
    apply Nat.leb_le in Hval.
    specialize (IHceval2 eq_refl).
    rewrite Hvi, Hlen in IHceval2.
    replace (S (vars s vi) - 1) with (vars s vi) in IHceval2 by lia.
    remember (length (arr s)) as n.
    remember (vars s vi) as i.
    assert (HBC : S i * i = i * (i - 1) + 2 * i).
    { destruct i; simpl; [reflexivity | nia]. }
    assert (HBA : S i * i <= n * (n - 1)).
    { destruct n as [|n']; [lia | ].
      replace (S n' - 1) with n' by lia.
      assert (i <= n') by lia. nia. }
    remember (n * (n - 1)) as A.
    remember (S i * i) as B.
    remember (i * (i - 1)) as C.
    clear HeqA HeqB HeqC Heqn Heqi.
    lia.
Qed.

(* Worst case: sorting a list of length n by this imperative insertion sort
   performs at most n*(n-1)/2 key comparisons, stated without division. *)
Theorem insertion_sort_while_comparisons_upper_bound :
  forall (l : list nat) (s' : state) (k : nat),
    ceval insertion_sort (init l) s' k ->
    2 * k <= length l * (length l - 1).
Proof.
  intros l s' k H. unfold insertion_sort in H.
  apply ceval_seq_inv in H. destruct H as [s1 [k1 [k2 [HI [HW Hk]]]]].
  apply ceval_ass_inv in HI. destruct HI as [Hs1 HkI]. subst k1 k.
  pose proof (outer_loop_bound _ _ _ HW) as Hob.
  assert (Hvi1 : vars s1 vi = 1) by (rewrite Hs1; unfold init, upd; simpl; reflexivity).
  assert (Hlen1 : length (arr s1) = length l) by (rewrite Hs1; unfold init; simpl; reflexivity).
  rewrite Hvi1, Hlen1 in Hob.
  replace (1 * (1 - 1)) with 0 in Hob by lia.
  rewrite Nat.sub_0_r in Hob.
  lia.
Qed.
