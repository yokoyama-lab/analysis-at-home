(* analysis@home — work unit: tree-mirror-size (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring a binary tree preserves its size. *)

Require Import Arith Lia.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint size (t:bt) := match t with Lf => 1 | Nd l r => S (size l + size r) end.
Fixpoint mirror (t:bt) := match t with Lf => Lf | Nd l r => Nd (mirror r) (mirror l) end.
Theorem tree_mirror_size : forall t, size (mirror t) = size t.
Proof. induction t as [|l IHl r IHr]; simpl. reflexivity. rewrite IHl, IHr. lia. Qed.
