(* analysis@home — work unit: tree-map-compose (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). map_tree g (map_tree f t) = map_tree (g . f) t. *)

Require Import Arith Lia.

Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint map_tree (f:nat->nat) (t:lt) := match t with LLf => LLf | LNd l k r => LNd (map_tree f l) (f k) (map_tree f r) end.
Theorem tree_map_compose : forall f g t, map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t.
Proof. intros f g t. induction t as [|l IHl k r IHr]; simpl. reflexivity. rewrite IHl, IHr. reflexivity. Qed.
