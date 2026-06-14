(* analysis@home — work unit: list-map-id (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). map id l = l. *)

Require Import List Arith Lia.
Import ListNotations.

Theorem list_map_id : forall l : list nat, map (fun x => x) l = l.
Proof. induction l as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
