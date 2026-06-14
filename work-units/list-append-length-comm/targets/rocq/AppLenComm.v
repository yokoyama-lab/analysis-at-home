(* analysis@home — work unit: list-append-length-comm (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). length(l1++l2) = length(l2++l1). *)

Require Import List Arith Lia.
Import ListNotations.

Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Theorem list_app_length_comm : forall l1 l2 : list nat, length (l1 ++ l2) = length (l2 ++ l1).
Proof. intros l1 l2. rewrite !app_len. lia. Qed.
