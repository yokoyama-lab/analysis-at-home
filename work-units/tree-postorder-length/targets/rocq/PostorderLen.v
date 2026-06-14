(* analysis@home — work unit: tree-postorder-length (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A postorder traversal of a tree with n nodes has length n. *)

Require Import List Arith Lia.
Import ListNotations.

Lemma app_len : forall l1 l2 : list nat, length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1 as [|x xs IH]; intro l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lsize (t:lt) := match t with LLf => 0 | LNd l _ r => S (lsize l + lsize r) end.
Fixpoint postorder (t:lt) : list nat := match t with LLf => [] | LNd l k r => postorder l ++ postorder r ++ [k] end.
Theorem tree_postorder_length : forall t, length (postorder t) = lsize t.
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity. rewrite app_len, app_len. simpl. rewrite IHl, IHr. lia. Qed.
