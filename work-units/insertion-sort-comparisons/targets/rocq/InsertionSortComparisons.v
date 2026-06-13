(* analysis@home — work unit: insertion-sort-comparisons (Rocq target)
 *
 * SEED FILE. The cost model (insert / isort / comparisons) is fixed and must
 * not change. The theorem below is the open claim: replace [Admitted.] with a
 * real proof. CI type-checks this file with coqc; [Admitted.] compiles (as an
 * axiom), so the seed is green until a real proof — verified by the kernel —
 * lands. *)

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
