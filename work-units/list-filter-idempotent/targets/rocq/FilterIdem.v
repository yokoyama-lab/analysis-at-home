(* analysis@home — work unit: list-filter-idempotent (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). filter p (filter p l) = filter p l. *)

Require Import List Arith Lia Bool.
Import ListNotations.

Theorem list_filter_idempotent : forall (p:nat->bool) l, filter p (filter p l) = filter p l.
Proof. intros p l. induction l as [|x xs IH]; simpl. reflexivity.
  destruct (p x) eqn:E; simpl. rewrite E, IH. reflexivity. exact IH. Qed.
