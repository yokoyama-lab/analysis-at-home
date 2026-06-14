(* analysis@home — work unit: perfect-tree-leaves (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A perfect binary tree of height h has 2^h leaves. *)

Require Import Arith Lia.

Inductive bt : Type := Lf | Nd (l r : bt).
Fixpoint leaves (t : bt) : nat := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint pt (h : nat) : bt := match h with 0 => Lf | S k => Nd (pt k) (pt k) end.
Theorem perfect_tree_leaves : forall h, leaves (pt h) = 2 ^ h.
Proof. induction h as [|k IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.
