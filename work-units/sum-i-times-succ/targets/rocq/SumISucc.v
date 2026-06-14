(* analysis@home — work unit: sum-i-times-succ (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of i(i+1) for i=1..n equals n(n+1)(n+2)/3. *)

Require Import Arith Lia.

Fixpoint sumprod (n : nat) : nat := match n with 0 => 0 | S m => sumprod m + (S m) * (S m + 1) end.
Theorem sum_i_succ : forall n, 3 * sumprod n = n * (n + 1) * (n + 2).
Proof. induction n as [|m IH]; simpl; nia. Qed.
