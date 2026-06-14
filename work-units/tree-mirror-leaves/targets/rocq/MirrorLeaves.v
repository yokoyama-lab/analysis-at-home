(* analysis@home — work unit: tree-mirror-leaves (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring a binary tree preserves its number of leaves. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint mirror (t:bt) := match t with Lf => Lf | Nd l r => Nd (mirror r) (mirror l) end.
Theorem mirror_leaves : forall t, leaves (mirror t) = leaves t.
Proof. induction t as [|l IHl r IHr]; simpl. reflexivity. rewrite IHl, IHr. lia. Qed.
