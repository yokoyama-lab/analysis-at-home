(* analysis@home — work unit: exp-by-squaring-correct (Rocq target).
 *
 * Exponentiation by squaring computes b^e with ~lg e multiplications by squaring
 * the half-power and multiplying in one extra factor on odd exponents:
 *   fastpow b e = fastpow b (e/2) ^... = (b^(e/2))^2 * b^(e mod 2),  fastpow b 0 = 1.
 * This is the CORRECTNESS twin of `fast-exponentiation-mults` (which counts the
 * multiplications). Theorem:
 *   fastpow_correct : e <= fuel -> fastpow fuel b e = b ^ e.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint fastpow (fuel b e : nat) : nat :=
  match fuel with
  | 0 => 1
  | S f => match e with
           | 0 => 1
           | S _ => fastpow f b (e / 2) * fastpow f b (e / 2) * b ^ (e mod 2)
           end
  end.

Theorem fastpow_correct : forall fuel b e, e <= fuel -> fastpow fuel b e = b ^ e.
Proof.
  induction fuel as [|f IH]; intros b e He.
  - assert (e = 0) by lia. subst. reflexivity.
  - destruct e as [|e']; [reflexivity|]. cbn [fastpow].
    assert (Hlt : S e' / 2 < S e') by (apply Nat.div_lt; lia).
    rewrite (IH b (S e' / 2)) by lia.
    rewrite <- !Nat.pow_add_r. f_equal.
    pose proof (Nat.div_mod_eq (S e') 2). lia.
Qed.
