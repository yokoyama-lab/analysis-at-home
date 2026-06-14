(* analysis@home — work unit: perfect-tree-height (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). The perfect binary tree pt h has height h. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint height (t:bt) := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.
Fixpoint pt (h:nat) := match h with 0 => Lf | S k => Nd (pt k) (pt k) end.
Theorem perfect_tree_height : forall h, height (pt h) = h.
Proof. induction h as [|k IH]; simpl. reflexivity. rewrite IH. rewrite Nat.max_id. reflexivity. Qed.
