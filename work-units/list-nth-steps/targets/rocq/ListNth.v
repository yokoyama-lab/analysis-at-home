(* analysis@home — work unit: list-nth-steps (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Accessing the k-th element walks at most n list cells. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint nthc (k : nat) (l : list nat) {struct l} : option nat * nat :=
  match l, k with
  | [], _ => (None, 0)
  | x :: _, 0 => (Some x, 1)
  | _ :: xs, S j => let '(r, c) := nthc j xs in (r, S c)
  end.
Theorem list_nth_steps : forall l k, snd (nthc k l) <= length l.
Proof. induction l as [|x xs IH]; intro k.
  - simpl. lia.
  - simpl. destruct k as [|j].
    + cbn [snd]. lia.
    + destruct (nthc j xs) as [r c] eqn:E. cbn [snd]. specialize (IH j).
      try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
