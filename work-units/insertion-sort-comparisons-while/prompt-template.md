<!--
Ready-to-paste prompt for a contributor's own LLM.
Copy everything below the line into your LLM (Claude, etc.), let it produce a
proof, then paste the resulting .v back into the project for kernel verification.
The project NEVER runs this prompt for you and never sees your credentials.
-->

---

You are completing a Rocq (Coq) proof for the analysis@home project.

Below is a complete, type-checking development of a small imperative WHILE
language with a big-step, cost-annotated semantics, an insertion-sort program
written in it, and one `Admitted.` theorem. Your task: **replace `Admitted.`
with a real proof** so the file compiles with `coqc` and contains no
`Admitted`/`admit`/`Axiom`/`sorry`. Do **not** change the semantics
(`aeval`/`beval`/`ceval`), the `insertion_sort` program, or the theorem
statement — only supply the proof.

The counted operation is the **key comparison** (`BKLe`, array element vs. the
held key); index tests (`BLe`) are free. The claim: any terminating run
performs at most `n(n-1)/2` key comparisons.

```coq
Require Import List Arith Lia.
Import ListNotations.

Definition vstore := nat -> nat.
Record state := mk_state { arr : list nat; vars : vstore }.

Definition upd (s : vstore) (x v : nat) : vstore :=
  fun y => if Nat.eqb x y then v else s y.

Fixpoint list_set (l : list nat) (i v : nat) : list nat :=
  match l, i with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S i' => h :: list_set t i' v
  end.

Inductive aexp : Type :=
| ANum (n : nat) | AVar (x : nat) | AArr (i : aexp) | ALen
| APlus (a1 a2 : aexp) | AMinus (a1 a2 : aexp) | AMult (a1 a2 : aexp).

Fixpoint aeval (s : state) (a : aexp) : nat :=
  match a with
  | ANum n => n | AVar x => vars s x
  | AArr i => nth (aeval s i) (arr s) 0 | ALen => length (arr s)
  | APlus a b => aeval s a + aeval s b
  | AMinus a b => aeval s a - aeval s b
  | AMult a b => aeval s a * aeval s b
  end.

Inductive bexp : Type :=
| BTrue | BFalse | BLe (a1 a2 : aexp) | BKLe (a1 a2 : aexp)
| BNot (b : bexp) | BAnd (b1 b2 : bexp).

Fixpoint beval (s : state) (b : bexp) : bool * nat :=
  match b with
  | BTrue => (true, 0) | BFalse => (false, 0)
  | BLe a1 a2 => (Nat.leb (aeval s a1) (aeval s a2), 0)
  | BKLe a1 a2 => (Nat.leb (aeval s a1) (aeval s a2), 1)
  | BNot b1 => let (v, c) := beval s b1 in (negb v, c)
  | BAnd b1 b2 =>
      let (v1, c1) := beval s b1 in
      if v1 then let (v2, c2) := beval s b2 in (v2, c1 + c2) else (false, c1)
  end.

Inductive com : Type :=
| CSkip | CAss (x : nat) (a : aexp) | CArrAss (i : aexp) (a : aexp)
| CSeq (c1 c2 : com) | CIf (b : bexp) (c1 c2 : com) | CWhile (b : bexp) (c : com).

Inductive ceval : com -> state -> state -> nat -> Prop :=
| E_Skip : forall s, ceval CSkip s s 0
| E_Ass : forall s x a,
    ceval (CAss x a) s (mk_state (arr s) (upd (vars s) x (aeval s a))) 0
| E_ArrAss : forall s i a,
    ceval (CArrAss i a) s
          (mk_state (list_set (arr s) (aeval s i) (aeval s a)) (vars s)) 0
| E_Seq : forall c1 c2 s s1 s2 k1 k2,
    ceval c1 s s1 k1 -> ceval c2 s1 s2 k2 -> ceval (CSeq c1 c2) s s2 (k1 + k2)
| E_IfTrue : forall b c1 c2 s s' kb k,
    beval s b = (true, kb) -> ceval c1 s s' k -> ceval (CIf b c1 c2) s s' (kb + k)
| E_IfFalse : forall b c1 c2 s s' kb k,
    beval s b = (false, kb) -> ceval c2 s s' k -> ceval (CIf b c1 c2) s s' (kb + k)
| E_WhileFalse : forall b c s kb,
    beval s b = (false, kb) -> ceval (CWhile b c) s s kb
| E_WhileTrue : forall b c s s1 s2 kb k1 k2,
    beval s b = (true, kb) -> ceval c s s1 k1 -> ceval (CWhile b c) s1 s2 k2 ->
    ceval (CWhile b c) s s2 (kb + k1 + k2).

Definition vi : nat := 0.  Definition vj : nat := 1.  Definition vkey : nat := 2.

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

Theorem insertion_sort_while_comparisons_upper_bound :
  forall (l : list nat) (s' : state) (k : nat),
    ceval insertion_sort (init l) s' k ->
    2 * k <= length l * (length l - 1).
Proof.
Admitted.
```

Hints (optional):
- Prove a lemma: any run of the inner `CWhile inner_guard ...` from a state with
  `vars s vj = m` performs ≤ `m` key comparisons (induction on the `ceval`
  derivation, using inversion on `E_WhileTrue`/`E_WhileFalse`).
- Then handle the outer loop with an invariant relating `vars s vi` to the
  comparisons accumulated so far; `lia` closes the arithmetic.

Return **only** the full Rocq source of the completed file, in a single code block.
