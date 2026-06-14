(* analysis@home — work unit: tree-fold-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Folding (summing) a labeled tree visits each node exactly once. *)

Require Import Arith Lia.
Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lsize (t:lt) := match t with LLf => 0 | LNd l _ r => S (lsize l + lsize r) end.
Fixpoint sumtree (t:lt) : nat * nat :=
  match t with LLf => (0,0) | LNd l k r => let '(sl,cl) := sumtree l in let '(sr,cr) := sumtree r in (sl+k+sr, S (cl+cr)) end.
Theorem tree_fold_operations : forall t, snd (sumtree t) = lsize t.
Proof. induction t as [|l IHl k r IHr]; simpl. reflexivity.
  destruct (sumtree l) as [sl cl] eqn:El. destruct (sumtree r) as [sr cr] eqn:Er. cbn [snd].
  try (rewrite El in IHl); try (rewrite Er in IHr). cbn [snd] in IHl, IHr. lia. Qed.
