(* analysis@home — work unit: horner-correct (Rocq target).
 *
 * Horner's rule evaluates a polynomial with n multiplications by nesting:
 *   horner [a0;a1;...;ak] x = a0 + x*(a1 + x*(... + x*ak))
 * This is the CORRECTNESS twin of `horner-multiplications` (which counts the n
 * multiplications). It computes exactly the polynomial sum:
 *   horner_correct : horner cs x = poly cs x   where poly cs x = Σ_i cs_i * x^i.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List.
Import ListNotations.

Fixpoint horner (cs : list nat) (x : nat) : nat :=
  match cs with [] => 0 | a :: t => a + x * horner t x end.

(* the polynomial as an explicit sum Σ cs_i * x^i (coefficient i carried in `i`) *)
Fixpoint powsum (cs : list nat) (x i : nat) : nat :=
  match cs with [] => 0 | a :: t => a * x ^ i + powsum t x (S i) end.
Definition poly (cs : list nat) (x : nat) : nat := powsum cs x 0.

Lemma powsum_horner : forall cs x i, powsum cs x i = x ^ i * horner cs x.
Proof.
  induction cs as [|a t IH]; intros x i; cbn [powsum horner].
  - ring.
  - rewrite IH, (Nat.pow_succ_r' x i). ring.
Qed.

Theorem horner_correct : forall cs x, horner cs x = poly cs x.
Proof.
  intros cs x. unfold poly. rewrite powsum_horner. cbn [Nat.pow]. ring.
Qed.
