(* analysis@home — work unit: list-rev-map (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). rev (map f l) = map f (rev l). *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_rev_map : forall (f:nat->nat) l, rev (map f l) = map f (rev l).
Proof. intros f l. induction l as [|x xs IH]; simpl. reflexivity. rewrite map_app. simpl. rewrite IH. reflexivity. Qed.
