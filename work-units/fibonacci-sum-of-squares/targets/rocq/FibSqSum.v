(* analysis@home — work unit: fibonacci-sum-of-squares (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). F_1^2 + ... + F_n^2 = F_n * F_{n+1}. *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Fixpoint ssq (n:nat) := match n with 0 => 0 | S m => ssq m + (fib (S m)) * (fib (S m)) end.
Theorem fib_sq_sum : forall n, ssq n = fib n * fib (S n).
Proof. induction n as [|m IH]; [reflexivity|].
  cbn [ssq]. rewrite IH. change (fib (S (S m))) with (fib (S m) + fib m). nia. Qed.
