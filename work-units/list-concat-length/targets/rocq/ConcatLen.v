(* analysis@home — work unit: list-concat-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). length (concat ls) = sum of the lengths of the inner lists. *)

Require Import List Arith Lia.
Import ListNotations.

Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Fixpoint sumlen (ls : list (list nat)) := match ls with [] => 0 | x :: xs => length x + sumlen xs end.
Theorem list_concat_length : forall ls, length (concat ls) = sumlen ls.
Proof. induction ls as [|x xs IH]; simpl. reflexivity. rewrite app_len, IH. reflexivity. Qed.
