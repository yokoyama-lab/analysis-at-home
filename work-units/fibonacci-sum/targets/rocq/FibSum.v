(* analysis@home — work unit: fibonacci-sum (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of the first n Fibonacci numbers is F(n+2) - 1. *)

Require Import Arith Lia.

Fixpoint fib (n : nat) : nat := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Fixpoint sumfib (n : nat) : nat := match n with 0 => 0 | S m => sumfib m + fib (S m) end.
Theorem fib_sum : forall n, sumfib n + 1 = fib (S (S n)).
Proof. induction n as [|m IH].
  - reflexivity.
  - change (sumfib (S m)) with (sumfib m + fib (S m)).
    change (fib (S (S (S m)))) with (fib (S (S m)) + fib (S m)). lia. Qed.
