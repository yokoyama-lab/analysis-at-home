(* analysis@home — shared spec (fixed) for the decomposed merge-sort unit. *)
Require Import List Arith Lia.
Import ListNotations.

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest => let (a, b) := split rest in (x :: a, y :: b)
  end.

Fixpoint merge (fuel : nat) (l1 l2 : list nat) : list nat * nat :=
  match fuel with
  | 0 => (l1 ++ l2, 0)
  | S f =>
      match l1, l2 with
      | [], _ => (l2, 0)
      | _, [] => (l1, 0)
      | x :: xs, y :: ys =>
          if x <=? y then let (m, c) := merge f xs l2 in (x :: m, S c)
          else            let (m, c) := merge f l1 ys in (y :: m, S c)
      end
  end.

Fixpoint msort (k : nat) (l : list nat) : list nat * nat :=
  match k with
  | 0 => (l, 0)
  | S k' =>
      match l with
      | [] => ([], 0)
      | [x] => ([x], 0)
      | _ =>
          let (l1, l2) := split l in
          let (s1, c1) := msort k' l1 in
          let (s2, c2) := msort k' l2 in
          let (m, cm) := merge (length s1 + length s2) s1 s2 in
          (m, c1 + c2 + cm)
      end
  end.

Definition comparisons (k : nat) (l : list nat) : nat := snd (msort k l).
