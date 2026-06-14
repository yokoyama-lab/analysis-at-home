(* analysis@home — work unit: list-map-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mapping a function over a list preserves its length. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_map_length : forall (f : nat -> nat) l, length (map f l) = length l.
Proof. intros f l. induction l as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
