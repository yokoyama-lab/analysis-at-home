(* analysis@home — work unit: tree-map-size (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mapping a function over a labeled tree preserves its size. *)

Require Import Arith Lia.
Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lsize (t:lt) := match t with LLf => 0 | LNd l _ r => S (lsize l + lsize r) end.
Fixpoint map_tree (f:nat->nat) (t:lt) := match t with LLf => LLf | LNd l k r => LNd (map_tree f l) (f k) (map_tree f r) end.
Theorem map_tree_size : forall f t, lsize (map_tree f t) = lsize t.
Proof. intros f t. induction t as [|l IHl k r IHr]; simpl. reflexivity. rewrite IHl, IHr. lia. Qed.
