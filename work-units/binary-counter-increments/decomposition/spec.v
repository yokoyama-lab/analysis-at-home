(* analysis@home — shared spec (fixed) for the decomposed binary-counter unit. *)
Require Import List Arith Lia.
Import ListNotations.

Fixpoint count_ones (bs : list bool) : nat :=
  match bs with
  | [] => 0
  | true :: r => S (count_ones r)
  | false :: r => count_ones r
  end.

Fixpoint incr (bs : list bool) : list bool * nat :=
  match bs with
  | [] => ([true], 1)
  | false :: r => (true :: r, 1)
  | true :: r => let (r', c) := incr r in (false :: r', S c)
  end.

Fixpoint incr_n (n : nat) : list bool * nat :=
  match n with
  | 0 => ([], 0)
  | S k => let (bs, tot) := incr_n k in
           let (bs', c) := incr bs in (bs', tot + c)
  end.

Definition flips (n : nat) : nat := snd (incr_n n).
