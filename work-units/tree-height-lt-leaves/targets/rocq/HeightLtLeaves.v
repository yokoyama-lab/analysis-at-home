(* analysis@home — work unit: tree-height-lt-leaves (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A binary tree's height is strictly less than its number of leaves. *)

Require Import Arith Lia.
Inductive bt := Lf | Nd (l r : bt).
Fixpoint leaves (t:bt) := match t with Lf => 1 | Nd l r => leaves l + leaves r end.
Fixpoint internal (t:bt) := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint height (t:bt) := match t with Lf => 0 | Nd l r => S (Nat.max (height l) (height r)) end.
Lemma h_le_i : forall t, height t <= internal t.
Proof. induction t as [|l IHl r IHr]; simpl. lia.
  pose proof (Nat.le_max_l (height l) (height r)); pose proof (Nat.le_max_r (height l) (height r)); lia. Qed.
Lemma l_eq_si : forall t, leaves t = S (internal t).
Proof. induction t as [|l IHl r IHr]; simpl; lia. Qed.
Theorem height_lt_leaves : forall t, height t < leaves t.
Proof. intro t. pose proof (h_le_i t). pose proof (l_eq_si t). lia. Qed.
