(* analysis@home — work unit: take-drop-append (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Splitting a list at position k and concatenating recovers the list. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint take (k : nat) (l : list nat) {struct l} := match k, l with 0, _ => [] | _, [] => [] | S j, x :: xs => x :: take j xs end.
Fixpoint drop (k : nat) (l : list nat) {struct l} := match k, l with 0, _ => l | _, [] => [] | S j, _ :: xs => drop j xs end.
Theorem take_drop_append : forall l k, take k l ++ drop k l = l.
Proof. induction l as [|x xs IH]; intro k; simpl. destruct k; reflexivity.
  destruct k as [|j]; simpl. reflexivity. rewrite IH. reflexivity. Qed.
