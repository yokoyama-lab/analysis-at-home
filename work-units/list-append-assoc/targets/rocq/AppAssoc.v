(* analysis@home — work unit: list-append-assoc (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). List concatenation is associative. *)

Require Import List Arith Lia.
Import ListNotations.
Theorem app_assoc_nat : forall l1 l2 l3 : list nat, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. induction l1 as [|x xs IH]; intros l2 l3; simpl. reflexivity. rewrite IH. reflexivity. Qed.
