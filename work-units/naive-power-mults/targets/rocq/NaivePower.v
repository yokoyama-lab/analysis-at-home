(* analysis@home — work unit: naive-power-mults (Rocq target)
 *
 * Cost model: func-ops / counts = ["multiplication"].  claim_kind: closed-form.
 *
 * VERIFIED (Print Assumptions: closed under the global context). Naive
 * exponentiation b^e by repeated multiplication uses exactly e multiplications
 * — contrast the fast-exponentiation-mults unit's logarithmic bound. The Rocq
 * target also proves correctness (value = b^e). lean/agda/isabelle are open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint powc (b e : nat) : nat * nat :=
  match e with 0 => (1, 0) | S k => let '(v, m) := powc b k in (b * v, S m) end.

Theorem naive_power_mults : forall b e, snd (powc b e) = e.
Proof.
  intros b. induction e as [|k IH].
  - reflexivity.
  - simpl. destruct (powc b k) as [v m] eqn:E. simpl.
    try (rewrite E in IH). simpl in IH. lia.
Qed.

(* Correctness companion: it computes the right power. *)
Theorem naive_power_correct : forall b e, fst (powc b e) = b ^ e.
Proof.
  intros b. induction e as [|k IH].
  - reflexivity.
  - simpl. destruct (powc b k) as [v m] eqn:E. simpl.
    try (rewrite E in IH). simpl in IH. rewrite IH. reflexivity.
Qed.
