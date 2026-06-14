(* analysis@home — work unit: list-rev-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). rev (l1 ++ l2) = rev l2 ++ rev l1. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_rev_append : forall l1 l2 : list nat, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. induction l1 as [|x xs IH]; intro l2; simpl. rewrite app_nil_r; reflexivity. rewrite IH, app_assoc; reflexivity. Qed.
