(* analysis@home — work unit: tree-mirror-height (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring a binary tree preserves its height. *)

Require Import Arith Lia.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint height (t:bt) := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.
Fixpoint mirror (t:bt) := match t with Lf => Lf | Nd l r => Nd (mirror r) (mirror l) end.
Theorem tree_mirror_height : forall t, height (mirror t) = height t.
Proof. induction t as [|l IHl r IHr]; simpl. reflexivity. rewrite IHl, IHr, Nat.max_comm. reflexivity. Qed.
