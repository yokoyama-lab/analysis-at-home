(* analysis@home — work unit: fibonacci-le-lucas (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Each Fibonacci number is at most the corresponding Lucas number. *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Fixpoint lucas (n:nat) := match n with 0 => 2 | S m => match m with 0 => 1 | S k => lucas m + lucas k end end.
Theorem fib_le_lucas : forall n, fib n <= lucas n.
Proof.
  assert (H : forall n, fib n <= lucas n /\ fib (S n) <= lucas (S n)).
  { induction n as [|m [IH1 IH2]].
    - simpl. split; lia.
    - split.
      + exact IH2.
      + change (fib (S (S m))) with (fib (S m) + fib m).
        change (lucas (S (S m))) with (lucas (S m) + lucas m). lia. }
  intro n. apply H.
Qed.
