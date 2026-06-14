(* analysis@home — work unit: tree-preorder-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A preorder traversal of a tree with n nodes produces a list of length n. *)

Require Import List Arith Lia.
Import ListNotations.
Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lsize (t:lt) := match t with LLf => 0 | LNd l _ r => S (lsize l + lsize r) end.
Fixpoint preorder (t:lt) : list nat := match t with LLf => [] | LNd l k r => k :: (preorder l ++ preorder r) end.
Theorem preorder_length : forall t, length (preorder t) = lsize t.
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity.
  first [rewrite app_length | rewrite length_app]. rewrite IHl, IHr. lia. Qed.
