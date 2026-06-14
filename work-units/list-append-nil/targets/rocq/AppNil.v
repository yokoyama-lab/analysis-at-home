(* analysis@home — work unit: list-append-nil (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). l ++ [] = l. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_app_nil : forall l : list nat, l ++ [] = l.
Proof. induction l as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
