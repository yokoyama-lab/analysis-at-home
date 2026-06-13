<!--
Ready-to-paste prompt for a contributor's own LLM.
Copy everything below the line into your LLM (Claude, etc.), let it produce a
proof, then paste the resulting .v back into the project for kernel verification.
The project NEVER runs this prompt for you and never sees your credentials.
-->

---

You are completing a Rocq (Coq) proof for the analysis@home project.

Below is a complete, type-checking development with one `Admitted.` theorem.
Your task: **replace `Admitted.` with a real proof** so the file compiles with
`coqc` and contains no `Admitted`/`admit`/axioms. Do not change the definitions
of `insert`, `isort`, or `comparisons`, and do not change the statement of the
theorem — only supply the proof.

```coq
Require Import List Arith Lia.
Import ListNotations.

(* Instrumented insertion: returns the updated list together with the number
   of key comparisons performed (each [x <=? y] test counts as one). *)
Fixpoint insert (x : nat) (l : list nat) : list nat * nat :=
  match l with
  | [] => ([x], 0)
  | y :: ys =>
      if x <=? y then (x :: y :: ys, 1)
      else let (l', c) := insert x ys in (y :: l', S c)
  end.

Fixpoint isort (l : list nat) : list nat * nat :=
  match l with
  | [] => ([], 0)
  | x :: xs =>
      let (xs', c1) := isort xs in
      let (l', c2) := insert x xs' in
      (l', c1 + c2)
  end.

Definition comparisons (l : list nat) : nat := snd (isort l).

(* Worst case: insertion sort uses at most n*(n-1)/2 key comparisons,
   stated without division. *)
Theorem insertion_sort_comparisons_upper_bound :
  forall l : list nat,
    2 * comparisons l <= length l * (length l - 1).
Proof.
Admitted.
```

Hints (optional):
- A useful lemma: the comparisons used by `insert x l` are `<= length l`, and
  `length (fst (insert x l)) = S (length l)`.
- Then induct on `l` for the main theorem; `lia` discharges the arithmetic.

Return **only** the full Rocq source of the completed file, in a single code
block.
