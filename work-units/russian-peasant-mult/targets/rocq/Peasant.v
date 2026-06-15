(* analysis@home — work unit: russian-peasant-mult (Rocq target).
 *
 * Russian peasant (Egyptian) multiplication computes a*b using only DOUBLING,
 * HALVING and ADDITION — no multiplication primitive:
 *   peasant a b = (a mod 2)*b + peasant (a/2) (2*b),  peasant 0 b = 0.
 * (At each step: halve a, double b, and add b iff a is odd.) Correctness:
 *   peasant_correct : a <= fuel -> peasant fuel a b = a * b.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint peasant (fuel a b : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => match a with
           | 0 => 0
           | S _ => a mod 2 * b + peasant f (a / 2) (2 * b)
           end
  end.

Theorem peasant_correct : forall fuel a b, a <= fuel -> peasant fuel a b = a * b.
Proof.
  induction fuel as [|f IH]; intros a b Ha.
  - assert (a = 0) by lia. subst. reflexivity.
  - destruct a as [|a']; [reflexivity|]. cbn [peasant].
    assert (Hlt : S a' / 2 < S a') by (apply Nat.div_lt; lia).
    rewrite (IH (S a' / 2) (2 * b)) by lia.
    pose proof (Nat.div_mod_eq (S a') 2). nia.
Qed.
