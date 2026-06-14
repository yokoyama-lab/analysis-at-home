(* analysis@home — work unit: tree-map-id (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). map_tree id t = t. *)

Require Import Arith Lia.

Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint map_tree (f:nat->nat) (t:lt) := match t with LLf => LLf | LNd l k r => LNd (map_tree f l) (f k) (map_tree f r) end.
Theorem tree_map_id : forall t, map_tree (fun x => x) t = t.
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity. rewrite IHl, IHr. reflexivity. Qed.
