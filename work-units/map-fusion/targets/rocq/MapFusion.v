(* analysis@home — work unit: map-fusion (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Two successive maps compose into one. *)

Require Import List Arith Lia.
Import ListNotations.
Theorem map_fusion : forall (f g : nat -> nat) l, map g (map f l) = map (fun x => g (f x)) l.
Proof. intros f g l. induction l as [|x xs IH]; simpl. reflexivity. rewrite IH. reflexivity. Qed.
