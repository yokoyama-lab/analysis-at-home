(* analysis@home — work unit: subtractive-gcd (Rocq target).
 *
 * Euclid's ORIGINAL algorithm used repeated subtraction, no division or
 * remainder: gcd(a,b) = gcd(a-b,b) when a >= b (and symmetrically). `subgcd`
 * implements exactly that, with a fuel bound a+b (the sum strictly decreases by
 * at least 1 each step). Correctness:
 *   subgcd_correct : a + b <= fuel -> subgcd fuel a b = Nat.gcd a b.
 * (Contrast `euclid-gcd`, which uses `mod`; this one is subtraction-only.)
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint subgcd (fuel a b : nat) : nat :=
  match fuel with
  | 0 => a
  | S f =>
      match a with
      | 0 => b
      | S _ => match b with
               | 0 => a
               | S _ => if a <? b then subgcd f a (b - a) else subgcd f b (a - b)
               end
      end
  end.

Theorem subgcd_correct : forall fuel a b, a + b <= fuel -> subgcd fuel a b = Nat.gcd a b.
Proof.
  induction fuel as [|f IH]; intros a b Hf.
  - assert (a = 0) by lia. assert (b = 0) by lia. subst. reflexivity.
  - destruct a as [|a']; [now rewrite Nat.gcd_0_l|].
    destruct b as [|b']; [now rewrite Nat.gcd_0_r|].
    cbn [subgcd]. destruct (S a' <? S b') eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite (IH (S a') (S b' - S a')) by lia.
      rewrite (Nat.gcd_sub_diag_r (S a') (S b') (Nat.lt_le_incl _ _ E)). reflexivity.
    + apply Nat.ltb_ge in E.
      rewrite (IH (S b') (S a' - S b')) by lia.
      rewrite (Nat.gcd_sub_diag_r (S b') (S a') E). apply Nat.gcd_comm.
Qed.
