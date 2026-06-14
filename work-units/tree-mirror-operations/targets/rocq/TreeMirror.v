(* analysis@home — work unit: tree-mirror-operations (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Mirroring touches each internal node once. *)

Require Import Arith Lia.

Inductive bt : Type := Lf | Nd (l r : bt).
Fixpoint internal (t : bt) : nat := match t with Lf => 0 | Nd l r => S (internal l + internal r) end.
Fixpoint mirrorc (t : bt) : bt * nat :=
  match t with
  | Lf => (Lf, 0)
  | Nd l r => let '(l', cl) := mirrorc l in let '(r', cr) := mirrorc r in (Nd r' l', S (cl + cr))
  end.
Theorem mirror_operations : forall t, snd (mirrorc t) = internal t.
Proof. induction t as [|l IHl r IHr]; simpl.
  - reflexivity.
  - destruct (mirrorc l) as [l' cl] eqn:El. destruct (mirrorc r) as [r' cr] eqn:Er. cbn [snd].
    try (rewrite El in IHl); try (rewrite Er in IHr). cbn [snd] in IHl, IHr. lia. Qed.
