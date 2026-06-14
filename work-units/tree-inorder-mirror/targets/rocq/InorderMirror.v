(* analysis@home — work unit: tree-inorder-mirror (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). inorder (mirror t) = rev (inorder t). *)

Require Import List Arith Lia.
Import ListNotations.

Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint inorder (t:lt) : list nat := match t with LLf => [] | LNd l k r => inorder l ++ (k :: inorder r) end.
Fixpoint lmirror (t:lt) := match t with LLf => LLf | LNd l k r => LNd (lmirror r) k (lmirror l) end.
Theorem tree_inorder_mirror : forall t, inorder (lmirror t) = rev (inorder t).
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity.
  rewrite IHl, IHr. rewrite rev_app_distr. simpl. rewrite <- app_assoc. reflexivity. Qed.
