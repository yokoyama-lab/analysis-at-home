(* analysis@home — work unit: seq-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The list of n consecutive integers from s has length n. *)

Require Import List Arith Lia.
Import ListNotations.
Theorem seq_len : forall n s, length (seq s n) = n.
Proof. induction n as [|m IH]; intro s; simpl. reflexivity. rewrite IH. reflexivity. Qed.
