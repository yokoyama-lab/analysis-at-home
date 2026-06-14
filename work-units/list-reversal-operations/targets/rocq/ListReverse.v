(* analysis@home — work unit: list-reversal-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Reversing a length-n list uses n cons operations. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint revc (acc l : list nat) : list nat * nat :=
  match l with [] => (acc, 0) | x :: xs => let '(r, c) := revc (x :: acc) xs in (r, S c) end.
Definition rev_list (l : list nat) := revc [] l.
Lemma revc_count : forall l acc, snd (revc acc l) = length l.
Proof. induction l as [|x xs IH]; intro acc.
  - reflexivity.
  - simpl. destruct (revc (x::acc) xs) as [r c] eqn:E. cbn [snd].
    specialize (IH (x::acc)). try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
Theorem reverse_operations : forall l, snd (rev_list l) = length l.
Proof. intro l. unfold rev_list. apply revc_count. Qed.
