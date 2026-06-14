(* analysis@home — work unit: tree-map-height (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mapping a function over a labeled tree preserves its height. *)

Require Import Arith Lia.

Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lheight (t:lt) := match t with LLf => 0 | LNd l _ r => S (Nat.max (lheight l) (lheight r)) end.
Fixpoint map_tree (f:nat->nat) (t:lt) := match t with LLf => LLf | LNd l k r => LNd (map_tree f l) (f k) (map_tree f r) end.
Theorem tree_map_height : forall f t, lheight (map_tree f t) = lheight t.
Proof. intros f t. induction t as [|l IHl k r IHr]; simpl. reflexivity. rewrite IHl, IHr. reflexivity. Qed.
