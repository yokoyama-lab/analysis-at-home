(* analysis@home — work unit: perfect-tree-internal (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Perfect tree of height h: internal nodes = 2^h - 1. *)

Require Import Arith Lia.

Inductive bt : Type := Lf | Nd (l r : bt).
Fixpoint internal (t : bt) : nat := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint pt (h : nat) : bt := match h with 0 => Lf | S k => Nd (pt k) (pt k) end.
Theorem perfect_tree_internal : forall h, S (internal (pt h)) = 2 ^ h.
Proof. induction h as [|k IH]; simpl; lia. Qed.
