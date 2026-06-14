(* analysis@home — work unit: tree-height-le-nodes (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Tree height <= number of internal nodes. *)

Require Import Arith Lia.

Inductive bt : Type := Lf | Nd (l r : bt).
Fixpoint internal (t : bt) : nat := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint height (t : bt) : nat := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.
Theorem tree_height_le_nodes : forall t, height t <= internal t.
Proof. induction t as [|l IHl r IHr]; simpl.
  - lia.
  - pose proof (Nat.le_max_l (height l) (height r));
    pose proof (Nat.le_max_r (height l) (height r)); lia. Qed.
