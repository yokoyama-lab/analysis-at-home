(* analysis@home — work unit: quicksort-average-comparisons (Rocq target)
 *
 * Cost model: func-ops / counts = ["comparison"].  claim_kind: expected-cost.
 * Input distribution: uniformly random permutation (equivalently, random pivot).
 *
 * The VERIFY-TRACK TWIN of the conjecture-track artifact
 * tools/conjecture/results/quicksort-average.json, computed by sympy in
 * tools/conjecture/cas_explore.py. The average key-comparison count of randomized
 * quicksort satisfies the reduced recurrence
 *   n·C(n) = (n+1)·C(n-1) + 2(n-1),   C(0) = 0
 * (itself derived from the full-history recurrence C(n)=(n-1)+(2/n)Σ_{k<n}C(k)).
 * Here C is the recurrence's solution and Cf its conjectured closed form; we prove
 *   C n == Cf n,   Cf n = 2(n+1)·H_n − 4n,   H_n = Σ_{i=1}^n 1/i.
 *
 * Worked in QArith (rationals + harmonic numbers). The induction step is exactly
 * the CAS certificate (the closed form solves the recurrence), re-checked by the
 * kernel via `field`. C 2 = 1, C 3 = 8/3, C 4 = 29/6 (the known small values).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import QArith.
Require Import ZArith Arith Lia.
Open Scope Q_scope.

Definition q (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma q_succ : forall n, q (S n) == q n + 1.
Proof.
  intro n. unfold q. rewrite Nat2Z.inj_succ. unfold Z.succ.
  rewrite inject_Z_plus. reflexivity.
Qed.

Lemma q_succ_pos : forall n, 0 < q (S n).
Proof.
  intro n. unfold q. rewrite Nat2Z.inj_succ.
  unfold Qlt. simpl. pose proof (Nat2Z.is_nonneg n). lia.
Qed.

Lemma q_succ_nonzero : forall n, ~ (q (S n) == 0).
Proof.
  intros n Hc. apply (Qlt_irrefl 0). rewrite <- Hc at 2. apply q_succ_pos.
Qed.

Fixpoint H (n : nat) : Q :=
  match n with
  | O => 0
  | S m => H m + / q (S m)
  end.

Fixpoint C (n : nat) : Q :=
  match n with
  | O => 0
  | S m => (q (S (S m)) * C m + 2 * q m) / q (S m)
  end.

Definition Cf (n : nat) : Q := 2 * q (S n) * H n - 4 * q n.

Lemma Cf_recurrence :
  forall m, q (S m) * Cf (S m) == q (S (S m)) * Cf m + 2 * q m.
Proof.
  intro m. unfold Cf.
  change (H (S m)) with (H m + / q (S m)).
  rewrite (q_succ (S m)). rewrite (q_succ m).
  field. rewrite <- (q_succ m). apply q_succ_nonzero.
Qed.

Theorem quicksort_average_closed_form : forall n, C n == Cf n.
Proof.
  induction n as [|m IH].
  - unfold Cf. vm_compute. reflexivity.
  - change (C (S m)) with ((q (S (S m)) * C m + 2 * q m) / q (S m)).
    rewrite IH.
    rewrite <- (Cf_recurrence m).
    field. apply q_succ_nonzero.
Qed.
