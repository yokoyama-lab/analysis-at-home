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
 * SEED FILE. The semantics and the [insertion_sort] program are fixed; the
 * theorem is the open claim — replace [Admitted.] with a real proof. CI
 * type-checks this file; [Admitted.] compiles. *)

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

Definition insertion_sort : com :=
  CSeq (CAss vi (ANum 1))
    (CWhile (BLe (APlus (AVar vi) (ANum 1)) ALen)
       (CSeq (CAss vkey (AArr (AVar vi)))
       (CSeq (CAss vj (AVar vi))
       (CSeq
          (CWhile inner_guard
             (CSeq (CArrAss (AVar vj) (AArr (AMinus (AVar vj) (ANum 1))))
                   (CAss vj (AMinus (AVar vj) (ANum 1)))))
       (CSeq (CArrAss (AVar vj) (AVar vkey))
             (CAss vi (APlus (AVar vi) (ANum 1)))))))).

Definition init (l : list nat) : state := mk_state l (fun _ => 0).

(* Worst case: sorting a list of length n by this imperative insertion sort
   performs at most n*(n-1)/2 key comparisons, stated without division. *)
Theorem insertion_sort_while_comparisons_upper_bound :
  forall (l : list nat) (s' : state) (k : nat),
    ceval insertion_sort (init l) s' k ->
    2 * k <= length l * (length l - 1).
Proof.
Admitted.
