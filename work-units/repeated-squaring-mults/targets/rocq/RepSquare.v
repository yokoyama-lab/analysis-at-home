(* analysis@home — work unit: repeated-squaring-mults (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). x^(2^k) by repeated squaring: k multiplications. *)

Require Import Arith Lia.

Fixpoint repsq (k x : nat) : nat * nat := match k with 0 => (x, 0) | S j => let '(v, c) := repsq j x in (v * v, S c) end.
Theorem repsq_mults : forall k x, snd (repsq k x) = k.
Proof. intros k x. induction k as [|j IH].
  - reflexivity.
  - simpl. destruct (repsq j x) as [v c] eqn:E. cbn [snd]. try (rewrite E in IH). cbn [snd] in IH. lia. Qed.
