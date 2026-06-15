(* analysis@home — work unit: integer-sqrt (Rocq target).
 *
 * The integer square root: isqrt n is the unique r with r^2 <= n < (r+1)^2.
 * `isqrt_aux` scans the candidate upward while (r+1)^2 <= n; with fuel S n it
 * always reaches the boundary. Correctness:
 *   isqrt_correct : isqrt n * isqrt n <= n /\ n < S (isqrt n) * S (isqrt n).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint isqrt_aux (fuel n r : nat) : nat :=
  match fuel with
  | 0 => r
  | S f => if S r * S r <=? n then isqrt_aux f n (S r) else r
  end.
Definition isqrt (n : nat) : nat := isqrt_aux (S n) n 0.

(* lower bound is an invariant: we only step to S r when (S r)^2 <= n *)
Lemma isqrt_aux_lo : forall fuel n r, r * r <= n -> isqrt_aux fuel n r * isqrt_aux fuel n r <= n.
Proof.
  induction fuel as [|f IH]; intros n r Hr; cbn [isqrt_aux]; [exact Hr|].
  destruct (S r * S r <=? n) eqn:E.
  - apply Nat.leb_le in E. apply IH, E.
  - exact Hr.
Qed.

(* upper bound: with enough fuel the scan reaches r with n < (S r)^2 *)
Lemma isqrt_aux_hi : forall fuel n r,
  r * r <= n -> n - r <= fuel -> n < S (isqrt_aux fuel n r) * S (isqrt_aux fuel n r).
Proof.
  induction fuel as [|f IH]; intros n r Hr Hf; cbn [isqrt_aux].
  - nia.
  - destruct (S r * S r <=? n) eqn:E.
    + apply Nat.leb_le in E. apply IH; [exact E | nia].
    + apply Nat.leb_gt in E. exact E.
Qed.

Theorem isqrt_correct : forall n,
  isqrt n * isqrt n <= n /\ n < S (isqrt n) * S (isqrt n).
Proof.
  intro n. unfold isqrt. split.
  - apply isqrt_aux_lo. lia.
  - apply isqrt_aux_hi; lia.
Qed.
