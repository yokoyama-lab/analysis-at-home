(* analysis@home — work unit: euclid-gcd (Rocq target)
 *
 * Cost model: func-ops / counts = ["division"].  claim_kind: complexity.
 *
 * TAOCP Vol. 1 §1.1 / Vol. 2 §4.5.2 — Algorithm E, the *first* algorithm in
 * The Art of Computer Programming. Fuel-bounded Euclidean algorithm returning
 * (gcd, #division-steps). Two axiom-free theorems:
 *
 *   euclid_steps_le : the number of division steps is at most the divisor b.
 *   euclid_correct  : with enough fuel (b <= fuel), it computes Nat.gcd a b.
 *
 * The step bound here is the easy linear one (b decreases by at least 1 each
 * step). Knuth's TIGHT bound — O(log b), with the worst case at consecutive
 * Fibonacci numbers (Lamé's theorem) — is a harder future unit.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint euclid (fuel a b : nat) : nat * nat :=
  match fuel with
  | 0 => (a, 0)
  | S f =>
      match b with
      | 0 => (a, 0)
      | S _ => let '(g, s) := euclid f b (a mod b) in (g, S s)
      end
  end.

(* Cost: at most b division steps. *)
Theorem euclid_steps_le : forall fuel a b, snd (euclid fuel a b) <= b.
Proof.
  induction fuel as [|f IH]; intros a b.
  - simpl. lia.
  - simpl. destruct b as [|b'].
    + simpl. lia.
    + destruct (euclid f (S b') (a mod S b')) as [g s] eqn:E. cbn [snd].
      pose proof (IH (S b') (a mod S b')) as Hs. rewrite E in Hs. cbn [snd] in Hs.
      assert (a mod S b' < S b') by (apply Nat.mod_upper_bound; lia). lia.
Qed.

(* Correctness: with enough fuel, euclid computes the gcd. *)
Theorem euclid_correct :
  forall fuel a b, b <= fuel -> fst (euclid fuel a b) = Nat.gcd a b.
Proof.
  induction fuel as [|f IH]; intros a b Hb.
  - assert (b = 0) by lia. subst. simpl. now rewrite Nat.gcd_0_r.
  - simpl. destruct b as [|b'].
    + simpl. now rewrite Nat.gcd_0_r.
    + destruct (euclid f (S b') (a mod S b')) as [g s] eqn:E. cbn [fst].
      assert (Hlt : a mod S b' < S b') by (apply Nat.mod_upper_bound; lia).
      assert (Hf : a mod S b' <= f) by lia.
      pose proof (IH (S b') (a mod S b') Hf) as Hc. rewrite E in Hc. cbn [fst] in Hc.
      rewrite Hc.
      rewrite (Nat.gcd_comm (S b') (a mod S b')).
      rewrite Nat.gcd_mod by lia.
      apply Nat.gcd_comm.
Qed.
