(* analysis@home — work unit: list-take-steps (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Taking a prefix uses at most n steps. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint takec (k : nat) (l : list nat) {struct l} : list nat * nat :=
  match k, l with
  | 0, _ => ([], 0)
  | _, [] => ([], 0)
  | S j, x :: xs => let '(r, c) := takec j xs in (x :: r, S c)
  end.
Theorem list_take_steps : forall l k, snd (takec k l) <= length l.
Proof. induction l as [|x xs IH]; intro k.
  - simpl. destruct k; simpl; lia.
  - simpl. destruct k as [|j].
    + cbn [snd]. lia.
    + destruct (takec j xs) as [r c] eqn:E. cbn [snd]. specialize (IH j).
      try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
