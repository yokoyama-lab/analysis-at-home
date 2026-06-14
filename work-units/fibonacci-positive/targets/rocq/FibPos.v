(* analysis@home — work unit: fibonacci-positive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every Fibonacci number after the 0th is positive. *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Theorem fib_positive : forall n, 1 <= fib (S n).
Proof. induction n as [|m IH]; simpl. lia. destruct m; simpl in *; lia. Qed.
