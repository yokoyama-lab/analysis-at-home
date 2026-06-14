(* analysis@home — work unit: tree-mirror-involutive (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring a binary tree twice yields the original tree. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint mirror (t:bt) := match t with Lf => Lf | Nd l r => Nd (mirror r) (mirror l) end.
Theorem mirror_involutive : forall t, mirror (mirror t) = t.
Proof. induction t as [|l IHl r IHr]; simpl. reflexivity. rewrite IHl, IHr. reflexivity. Qed.
