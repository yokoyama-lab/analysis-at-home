(* analysis@home — work unit: tree-internal-lt-size (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree has strictly fewer internal nodes than total nodes. *)

Require Import Arith Lia.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint internal (t:bt) := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint size (t:bt) := match t with Lf => 1 | Nd l r => S (size l + size r) end.
Theorem tree_internal_lt_size : forall t, internal t < size t.
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
