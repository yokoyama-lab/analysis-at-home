(* analysis@home — work unit: filter-length-le (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Filtering a list yields a list no longer than the original. *)

Require Import List Arith Lia.
Import ListNotations.
Theorem filter_length_le : forall (p : nat -> bool) l, length (filter p l) <= length l.
Proof. intros p l. induction l as [|x xs IH]; simpl. lia. destruct (p x); simpl; lia. Qed.
