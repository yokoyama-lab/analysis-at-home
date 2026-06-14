(* analysis@home — work unit: list-drop-steps (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Dropping a prefix uses at most n steps. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint dropc (k : nat) (l : list nat) {struct l} : list nat * nat :=
  match k, l with
  | 0, _ => (l, 0)
  | _, [] => ([], 0)
  | S j, _ :: xs => let '(r, c) := dropc j xs in (r, S c)
  end.
Theorem list_drop_steps : forall l k, snd (dropc k l) <= length l.
Proof. induction l as [|x xs IH]; intro k.
  - simpl. destruct k; simpl; lia.
  - simpl. destruct k as [|j].
    + cbn [snd]. lia.
    + destruct (dropc j xs) as [r c] eqn:E. cbn [snd]. specialize (IH j).
      try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
