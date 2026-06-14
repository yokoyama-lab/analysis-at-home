(* analysis@home — work unit: tree-leaves-internal (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree has one more leaf than internal nodes. *)

Require Import Arith Lia.

Inductive bt : Type := Lf | Nd (l r : bt).
Fixpoint leaves (t : bt) : nat := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint internal (t : bt) : nat := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Theorem leaves_internal : forall t, leaves t = S (internal t).
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
