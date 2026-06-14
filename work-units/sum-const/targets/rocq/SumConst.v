(* analysis@home — work unit: sum-const (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Adding a constant c, n times, gives c*n. *)

Require Import Arith Lia.

Fixpoint sumconst (c n : nat) : nat := match n with 0 => 0 | S m => sumconst c m + c end.
Theorem sum_const : forall c n, sumconst c n = c * n.
Proof. intros c n. induction n as [|m IH]; simpl; nia. Qed.
