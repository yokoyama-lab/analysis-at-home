(* analysis@home — work unit: bst-insert-size (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Inserting into a binary search tree increases the size by at most one. *)

Require Import Arith Lia.
Inductive lt := LLf | LNd (l : lt) (k : nat) (r : lt).
Fixpoint lsize (t : lt) := match t with LLf => 0 | LNd l _ r => S (lsize l + lsize r) end.
Fixpoint insertc (x : nat) (t : lt) : lt * nat :=
  match t with
  | LLf => (LNd LLf x LLf, 0)
  | LNd l k r => if x =? k then (LNd l k r, 1)
                 else if x <? k then let '(l', c) := insertc x l in (LNd l' k r, S c)
                 else let '(r', c) := insertc x r in (LNd l k r', S c)
  end.
Theorem bst_insert_size : forall t x, lsize (fst (insertc x t)) <= S (lsize t).
Proof. induction t as [|l IHl k r IHr]; intro x; simpl.
  - lia.
  - destruct (x =? k).
    + cbn [fst]. simpl lsize. lia.
    + destruct (x <? k).
      * destruct (insertc x l) as [l' c] eqn:E. cbn [fst]. specialize (IHl x).
        try (rewrite E in IHl). cbn [fst] in IHl. simpl lsize. lia.
      * destruct (insertc x r) as [r' c] eqn:E. cbn [fst]. specialize (IHr x).
        try (rewrite E in IHr). cbn [fst] in IHr. simpl lsize. lia. Qed.
