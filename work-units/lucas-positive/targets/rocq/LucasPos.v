(* analysis@home — work unit: lucas-positive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every Lucas number is at least 1. *)

Require Import Arith Lia.

Fixpoint lucas (n:nat) := match n with 0 => 2 | S m => match m with 0 => 1 | S k => lucas m + lucas k end end.
Theorem lucas_positive : forall n, 1 <= lucas n.
Proof. induction n as [|m IH]; simpl. lia. destruct m; simpl in *; lia. Qed.
