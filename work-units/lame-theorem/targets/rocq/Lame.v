(* analysis@home — work unit: lame-theorem (Rocq target).
 *
 * Lamé's theorem (TAOCP Vol. 2 §4.5.3): the WORST case of the Euclidean
 * algorithm for a given number of division steps is consecutive Fibonacci
 * numbers. Concretely, if `steps fuel a b = n` with n >= 1 and a > b, then
 *   b >= F(n+1)  and  a >= F(n+2).
 * This is the tight O(log) bound behind the easy linear bound proved in the
 * `euclid-gcd` unit, and it ties together the `euclid-*` and `fibonacci-*`
 * corpora. `steps` mirrors `snd (euclid ...)` of that unit.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint fib (n:nat) := match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. reflexivity. Qed.

Fixpoint steps (fuel a b : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => match b with 0 => 0 | S _ => S (steps f b (a mod b)) end
  end.

(* Lamé's theorem: if Euclid's algorithm performs n >= 1 division steps on
   a > b, then b >= F(n+1) and a >= F(n+2). Consecutive Fibonacci numbers are
   thus the smallest pair forcing a given number of steps. *)
Theorem lame :
  forall fuel a b n, b < fuel -> b < a -> steps fuel a b = n -> 1 <= n ->
    fib (S n) <= b /\ fib (S (S n)) <= a.
Proof.
  induction fuel as [|f IH]; intros a b n Hbf Hba Hst Hn.
  - lia.
  - cbn [steps] in Hst. destruct b as [|b'].
    + (* b = 0: steps reduced to 0, contradicts 1 <= n *) lia.
    + (* b = S b' *)
      assert (Hrb : a mod (S b') < S b') by (apply Nat.mod_upper_bound; lia).
      destruct (steps f (S b') (a mod (S b'))) as [|m] eqn:Em.
      * (* subcall took 0 steps -> n = 1 *)
        assert (n = 1) by lia. subst n. cbn [fib]. split; lia.
      * (* subcall took S m >= 1 steps -> n = S (S m) *)
        assert (n = S (S m)) by lia. subst n.
        assert (Hrf : a mod (S b') < f) by lia.
        destruct (IH (S b') (a mod (S b')) (S m) Hrf Hrb Em ltac:(lia)) as [Hr Hb].
        (* Hr : fib (S (S m)) <= a mod (S b')  ;  Hb : fib (S (S (S m))) <= S b' *)
        assert (Hge : S b' + a mod (S b') <= a).
        { pose proof (Nat.div_mod_eq a (S b')) as Hdm.
          destruct (a / S b') as [|q].
          - rewrite Nat.mul_0_r in Hdm. lia.
          - rewrite Nat.mul_succ_r in Hdm. lia. }
        split.
        -- (* fib (S (S (S m))) <= S b' *) exact Hb.
        -- (* fib (S (S (S (S m)))) <= a *) rewrite (fib_SS (S (S m))). lia.
Qed.

(* Headline corollary: n >= 1 steps forces the divisor b >= F(n+1). *)
Corollary lame_divisor_bound :
  forall fuel a b n, b < fuel -> b < a -> steps fuel a b = n -> 1 <= n ->
    fib (S n) <= b.
Proof. intros fuel a b n H1 H2 H3 H4. now destruct (lame fuel a b n H1 H2 H3 H4). Qed.
