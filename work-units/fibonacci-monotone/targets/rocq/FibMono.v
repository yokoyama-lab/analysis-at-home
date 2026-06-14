(* analysis@home — work unit: fibonacci-monotone (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). F(n) <= F(n+1). *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Theorem fib_monotone : forall n, fib n <= fib (S n).
Proof. induction n as [|m IH]; [simpl; lia|]. simpl. destruct m; simpl; lia. Qed.
