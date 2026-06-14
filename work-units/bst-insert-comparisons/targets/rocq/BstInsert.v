(* analysis@home — work unit: bst-insert-comparisons (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Inserting into a binary search tree uses at most height+1 comparisons. *)

Require Import Arith Lia.
Inductive lt := LLf | LNd (l:lt) (k:nat) (r:lt).
Fixpoint lheight (t:lt) := match t with LLf => 0 | LNd l _ r => S (Nat.max (lheight l) (lheight r)) end.
Fixpoint insertc (x:nat) (t:lt) : lt * nat :=
  match t with
  | LLf => (LNd LLf x LLf, 0)
  | LNd l k r => if x =? k then (LNd l k r, 1)
                 else if x <? k then let '(l',c) := insertc x l in (LNd l' k r, S c)
                 else let '(r',c) := insertc x r in (LNd l k r', S c)
  end.
Theorem bst_insert_comparisons : forall t x, snd (insertc x t) <= S (lheight t).
Proof. induction t as [|l IHl k r IHr]; intro x; simpl.
  - lia.
  - destruct (x =? k).
    + cbn [snd]. lia.
    + destruct (x <? k).
      * destruct (insertc x l) as [l' c] eqn:E. cbn [snd]. specialize (IHl x).
        try (rewrite E in IHl). cbn [snd] in IHl.
        pose proof (Nat.le_max_l (lheight l) (lheight r)). lia.
      * destruct (insertc x r) as [r' c] eqn:E. cbn [snd]. specialize (IHr x).
        try (rewrite E in IHr). cbn [snd] in IHr.
        pose proof (Nat.le_max_r (lheight l) (lheight r)). lia. Qed.
