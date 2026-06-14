(* analysis@home — work unit: fibonacci-le-pow (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The n-th Fibonacci number is at most 2^n. *)

Require Import Arith Lia.

Fixpoint fib (n : nat) : nat := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Theorem fib_le_pow : forall n, fib n <= 2 ^ n.
Proof.
  assert (H : forall n, fib n <= 2 ^ n /\ fib (S n) <= 2 ^ (S n)).
  { induction n as [|m [IH1 IH2]].
    - simpl. split; lia.
    - split.
      + exact IH2.
      + change (fib (S (S m))) with (fib (S m) + fib m).
        assert (P : 2 ^ S (S m) = 2 * (2 * 2 ^ m)) by (simpl; lia).
        assert (Q : 2 ^ S m = 2 * 2 ^ m) by (simpl; lia).
        rewrite Q in IH2. rewrite P. nia. }
  intro n. apply H. Qed.
