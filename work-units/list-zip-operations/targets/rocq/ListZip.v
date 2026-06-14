(* analysis@home — work unit: list-zip-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Zipping two lists uses at most length(l1) pairing operations. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint zipc (l1 l2 : list nat) : list (nat*nat) * nat :=
  match l1 with
  | [] => ([], 0)
  | x :: xs => match l2 with
               | [] => ([], 1)
               | y :: ys => let '(r, c) := zipc xs ys in ((x,y) :: r, S c)
               end
  end.
Theorem list_zip_operations : forall l1 l2, snd (zipc l1 l2) <= length l1.
Proof. induction l1 as [|x xs IH]; intro l2.
  - simpl. lia.
  - simpl. destruct l2 as [|y ys].
    + cbn [snd]. lia.
    + destruct (zipc xs ys) as [r c] eqn:E. cbn [snd]. specialize (IH ys).
      try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
