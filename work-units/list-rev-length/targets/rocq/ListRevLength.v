(* analysis@home — work unit: list-rev-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Reversing a list preserves its length. *)

Require Import List Arith Lia.
Import ListNotations.

Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Theorem list_rev_length : forall l : list nat, length (rev l) = length l.
Proof. induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite app_len. simpl. lia. Qed.
