(* analysis@home — work unit: repeat-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Replicating x exactly n times yields a list of length n. *)

Require Import List Arith Lia.
Import ListNotations.
Theorem repeat_len : forall (x n : nat), length (repeat x n) = n.
Proof. intros x n. induction n as [|m IH]; simpl. reflexivity. rewrite IH. reflexivity. Qed.
