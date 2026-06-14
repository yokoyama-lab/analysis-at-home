(* analysis@home — work unit: two-pow-le-factorial (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Powers of two are bounded by the factorial. *)

Require Import Arith Lia.

Fixpoint fact (n:nat) := match n with 0 => 1 | S m => S m * fact m end.
Theorem two_pow_le_factorial : forall n, 2 ^ n <= fact (S n).
Proof. induction n as [|m IH].
  - simpl. lia.
  - assert (E1 : 2 ^ S m = 2 * 2 ^ m) by reflexivity.
    assert (E2 : fact (S (S m)) = S (S m) * fact (S m)) by reflexivity.
    rewrite E1, E2.
    apply Nat.le_trans with (2 * fact (S m)).
    + apply Nat.mul_le_mono_l. exact IH.
    + apply Nat.mul_le_mono_r. lia. Qed.
