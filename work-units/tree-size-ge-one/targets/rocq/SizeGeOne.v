(* analysis@home — work unit: tree-size-ge-one (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree has at least one node. *)

Require Import Arith Lia.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint size (t:bt) := match t with Lf => 1 | Nd l r => S (size l + size r) end.
Theorem tree_size_ge_one : forall t, 1 <= size t.
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
