(* analysis@home — shared spec (fixed) for the decomposed selection-sort unit. *)
Require Import List Arith Lia.
Import ListNotations.

Fixpoint select (x : nat) (l : list nat) : nat * list nat * nat :=
  match l with
  | [] => (x, [], 0)
  | y :: ys =>
      let '(m, rest, c) := select (if y <? x then y else x) ys in
      (m, (if y <? x then x else y) :: rest, S c)
  end.

Fixpoint ssort (fuel : nat) (l : list nat) : list nat * nat :=
  match fuel with
  | 0 => ([], 0)
  | S f =>
      match l with
      | [] => ([], 0)
      | x :: xs =>
          let '(m, rest, c1) := select x xs in
          let '(sorted, c2) := ssort f rest in
          (m :: sorted, c1 + c2)
      end
  end.

Definition comparisons (l : list nat) : nat := snd (ssort (length l) l).
