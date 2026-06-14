(* analysis@home — work unit: list-snoc-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). length (l ++ [x]) = length l + 1. *)

Require Import List Arith Lia.
Import ListNotations.

Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Theorem list_snoc_length : forall (l:list nat) x, length (l ++ [x]) = S (length l).
Proof. intros l x. rewrite app_len. simpl. lia. Qed.
