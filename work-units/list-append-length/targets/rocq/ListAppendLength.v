(* analysis@home — work unit: list-append-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The length of l1 ++ l2 is length l1 + length l2. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_append_length : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
