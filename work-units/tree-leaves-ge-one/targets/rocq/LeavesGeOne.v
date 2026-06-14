(* analysis@home — work unit: tree-leaves-ge-one (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Every binary tree has at least one leaf. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Theorem leaves_ge_one : forall t, 1 <= leaves t.
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
