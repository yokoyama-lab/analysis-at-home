(* analysis@home — work unit: tower-of-hanoi-moves (Rocq target)
 *
 * Cost model: func-ops / counts = ["move"].  claim_kind: closed-form.
 *
 * VERIFIED (Print Assumptions: closed under the global context). The Tower of
 * Hanoi for n disks takes exactly 2^n - 1 moves; stated division/subtraction-
 * free as hanoi_moves n + 1 = 2 ^ n. The lean/agda/isabelle targets are open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint hanoi_moves (n : nat) : nat :=
  match n with 0 => 0 | S k => 2 * hanoi_moves k + 1 end.

Theorem hanoi_moves_closed : forall n, hanoi_moves n + 1 = 2 ^ n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl hanoi_moves. rewrite Nat.pow_succ_r'. lia.
Qed.
