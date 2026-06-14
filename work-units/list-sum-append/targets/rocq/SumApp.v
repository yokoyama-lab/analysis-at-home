(* analysis@home — work unit: list-sum-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The sum of l1 ++ l2 is the sum of l1 plus the sum of l2. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint lsum (l : list nat) := match l with [] => 0 | x :: xs => x + lsum xs end.
Theorem list_sum_append : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl. reflexivity. rewrite IH. lia. Qed.
