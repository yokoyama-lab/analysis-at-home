(* analysis@home — work unit: tree-preorder-mirror (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). preorder (mirror t) = rev (postorder t). *)

Require Import List Arith Lia.
Import ListNotations.

Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint preorder (t:lt) : list nat := match t with LLf => [] | LNd l k r => k :: (preorder l ++ preorder r) end.
Fixpoint postorder (t:lt) : list nat := match t with LLf => [] | LNd l k r => postorder l ++ postorder r ++ [k] end.
Fixpoint lmirror (t:lt) := match t with LLf => LLf | LNd l k r => LNd (lmirror r) k (lmirror l) end.
Theorem tree_preorder_mirror : forall t, preorder (lmirror t) = rev (postorder t).
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity.
  rewrite IHl, IHr. rewrite !rev_app_distr. simpl. reflexivity. Qed.
