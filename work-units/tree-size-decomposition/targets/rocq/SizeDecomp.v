(* analysis@home — work unit: tree-size-decomposition (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree's size equals its leaves plus its internal nodes. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint internal (t:bt) := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint size (t:bt) := match t with Lf => 1 | Nd l r => S (size l + size r) end.
Theorem size_leaves_internal : forall t, size t = leaves t + internal t.
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
