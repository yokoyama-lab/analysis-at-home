(* analysis@home — work unit: lucas-numbers-sum (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). L_1 + ... + L_n = L_{n+2} - 3 (Lucas analogue of the Fibonacci sum). *)

Require Import Arith Lia.

Fixpoint lucas (n:nat) := match n with 0 => 2 | S m => match m with 0 => 1 | S k => lucas m + lucas k end end.
Fixpoint lsum (n:nat) := match n with 0 => 0 | S m => lsum m + lucas (S m) end.
Theorem lucas_sum : forall n, lsum n + 3 = lucas (S (S n)).
Proof. induction n as [|m IH].
  - reflexivity.
  - change (lsum (S m)) with (lsum m + lucas (S m)).
    change (lucas (S (S (S m)))) with (lucas (S (S m)) + lucas (S m)). lia. Qed.
