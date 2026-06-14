(* analysis@home — work unit: list-concat-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). concat (ls1 ++ ls2) = concat ls1 ++ concat ls2. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_concat_append : forall ls1 ls2 : list (list nat), concat (ls1 ++ ls2) = concat ls1 ++ concat ls2.
Proof. induction ls1 as [|x xs IH]; intro ls2; simpl. reflexivity. rewrite IH, app_assoc. reflexivity. Qed.
