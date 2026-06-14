(* analysis@home — work unit: factorial-mults (Rocq target)
 * Cost model: func-ops / counts = ["multiplication"].  claim_kind: closed-form.
 * VERIFIED (Print Assumptions: closed under the global context). Computing n!
 * by repeated multiplication uses exactly n-1 multiplications. lean/agda/isabelle open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint factc (n : nat) : nat * nat :=
  match n with
  | 0 => (1, 0)
  | S k => match k with
           | 0 => (1, 0)
           | _ => let '(v, m) := factc k in (S k * v, S m)
           end
  end.

Theorem factorial_mults : forall n, snd (factc n) = n - 1.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl. destruct k as [|k'].
    + reflexivity.
    + destruct (factc (S k')) as [v m] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. simpl. lia.
Qed.
