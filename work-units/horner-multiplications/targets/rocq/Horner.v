(* analysis@home — work unit: horner-multiplications (Rocq target)
 *
 * Cost model: func-ops / counts = ["multiplication"].  claim_kind: closed-form.
 *
 * VERIFIED (Print Assumptions: closed under the global context). Evaluating a
 * polynomial with k coefficients by Horner's rule uses exactly k-1
 * multiplications. The lean/agda/isabelle targets are open. *)

Require Import List Arith Lia.
Import ListNotations.

(* horner x [c0; c1; ...] computes the polynomial value (Horner form) together
   with the number of multiplications performed. *)
Fixpoint horner (x : nat) (coeffs : list nat) : nat * nat :=
  match coeffs with
  | [] => (0, 0)
  | c :: rest =>
      match rest with
      | [] => (c, 0)
      | _ => let '(v, m) := horner x rest in (c + x * v, S m)
      end
  end.

Theorem horner_mults_linear : forall x coeffs,
  snd (horner x coeffs) = length coeffs - 1.
Proof.
  intros x. induction coeffs as [|c rest IH].
  - reflexivity.
  - simpl. destruct rest as [|c' rest'].
    + reflexivity.
    + destruct (horner x (c' :: rest')) as [v m] eqn:E. simpl.
      try (rewrite E in IH). simpl in IH. simpl. lia.
Qed.
