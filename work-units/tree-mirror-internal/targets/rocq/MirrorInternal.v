(* analysis@home — work unit: tree-mirror-internal (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring a binary tree preserves its number of internal nodes. *)

Require Import Arith Lia.

Inductive bt := Lf | Nd (l r : bt).
Fixpoint internal (t:bt) := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint mirror (t:bt) := match t with Lf => Lf | Nd l r => Nd (mirror r) (mirror l) end.
Theorem tree_mirror_internal : forall t, internal (mirror t) = internal t.
Proof. induction t as [|l IHl r IHr]; simpl. reflexivity. rewrite IHl, IHr. lia. Qed.
