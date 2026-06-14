(* analysis@home — work unit: iterative-fibonacci-additions (Rocq target)
 * Cost model: func-ops / counts = ["addition"].  claim_kind: closed-form.
 * VERIFIED (Print Assumptions: closed under the global context). Iterative
 * Fibonacci (two accumulators) uses exactly n additions for n steps — contrast
 * the exponential call count of naive recursion. lean/agda/isabelle open. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint fibc (a b n : nat) : nat * nat :=
  match n with 0 => (a, 0) | S k => let '(r, m) := fibc b (a + b) k in (r, S m) end.

Theorem iterative_fibonacci_additions : forall n a b, snd (fibc a b n) = n.
Proof.
  induction n as [|k IH]; intros a b.
  - reflexivity.
  - simpl. destruct (fibc b (a + b) k) as [r m] eqn:E. simpl.
    specialize (IH b (a + b)). rewrite E in IH. simpl in IH. lia.
Qed.
