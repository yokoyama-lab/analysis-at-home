(* analysis@home — work unit: classical-addition (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Adding two n-digit numbers uses exactly n digit-additions. *)

Require Import List Arith Lia.
Import ListNotations.

Fixpoint addc (a b : list nat) {struct a} : nat :=
  match a, b with x::xs, y::ys => S (addc xs ys) | _, _ => 0 end.
Theorem classical_addition : forall a b, length a = length b -> addc a b = length a.
Proof. induction a as [|x xs IH]; intros [|y ys] H; simpl in *.
  - reflexivity. - reflexivity. - discriminate. - rewrite IH by lia. reflexivity. Qed.
