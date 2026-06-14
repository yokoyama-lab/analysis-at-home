(* analysis@home — work unit: geometric-weighted-sum (Rocq target)
 *
 * Cost model: func-ops / counts = ["operation"].  claim_kind: closed-form.
 *
 * The VERIFY-TRACK TWIN of the conjecture-track artifact
 * tools/conjecture/results/closed-form-sum-k2k.json. The conjecture track finds,
 * by a Gosper-style antidifference, the closed form
 *   Σ_{k=0}^{n-1} k·2^k = (n-2)·2^n + 2
 * together with the TELESCOPING CERTIFICATE  F(k+1) - F(k) = k·2^k  for
 * F(k) = (k-2)·2^k. Here the kernel re-checks the certificate by a routine
 * induction. The closed form is stated in nat without subtraction as
 *   wsum n + 2·2^n = n·2^n + 2.
 *
 * Σ k·2^k is the total work in a depth-weighted binary recursion (k units of
 * work at each of the 2^k nodes on level k).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => 2 * pow2 m
  end.

(* wsum n = Σ_{k=0}^{n-1} k * 2^k *)
Fixpoint wsum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => wsum m + m * pow2 m
  end.

Theorem geometric_weighted_sum :
  forall n, wsum n + 2 * pow2 n = n * pow2 n + 2.
Proof.
  induction n as [|m IH].
  - reflexivity.
  - simpl. remember (pow2 m) as p eqn:Ep. clear Ep.
    (* IH : wsum m + 2 * p = m * p + 2
       goal: wsum m + m * p + 2 * (2 * p) = S m * (2 * p) + 2 *)
    nia.
Qed.
