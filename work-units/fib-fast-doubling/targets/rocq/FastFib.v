(* analysis@home — work unit: fib-fast-doubling (Rocq target).
 *
 * The fast-doubling method computes Fibonacci numbers in O(log n) arithmetic
 * operations (vs O(n) for the naive recurrence), by recursing on the BITS of n
 * through the doubling identities
 *   fib(2k)   = fib k * (2*fib(k+1) − fib k)
 *   fib(2k+1) = fib k ^2 + fib(k+1) ^2
 * `fastpair n` returns the pair (fib n, fib (n+1)); correctness:
 *   fast_fib : n <= fuel -> fastpair fuel n = (fib n, fib (S n)).
 * The doubling identities follow from the addition formula fib(m+n+1) =
 * fib(m+1)fib(n+1) + fib(m)fib(n), proved by two-step induction.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint fib (n : nat) :=
  match n with 0 => 0 | S m => match m with 0 => 1 | S k => fib m + fib k end end.
Lemma fib_SSn : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. reflexivity. Qed.

(* addition formula via two-step induction *)
Lemma fib_add_aux : forall n m,
  fib (m + S n) = fib (S m) * fib (S n) + fib m * fib n /\
  fib (m + S (S n)) = fib (S m) * fib (S (S n)) + fib m * fib (S n).
Proof.
  induction n as [|n IH]; intro m.
  - split.
    + replace (m + 1) with (S m) by lia. change (fib 1) with 1. change (fib 0) with 0. lia.
    + replace (m + 2) with (S (S m)) by lia. rewrite (fib_SSn m).
      change (fib 2) with 1. change (fib 1) with 1. lia.
  - destruct (IH m) as [IH1 IH2]. split; [exact IH2|].
    replace (m + S (S (S n))) with (S (S (m + S n))) by lia.
    rewrite fib_SSn. replace (S (m + S n)) with (m + S (S n)) by lia.
    rewrite IH1, IH2. rewrite (fib_SSn (S n)), (fib_SSn n). ring.
Qed.

Lemma fib_add : forall n m,
  fib (m + S n) = fib (S m) * fib (S n) + fib m * fib n.
Proof. intros n m. apply (fib_add_aux n m). Qed.

Lemma fib_two_kp1 : forall k, fib (2 * k + 1) = fib k * fib k + fib (S k) * fib (S k).
Proof. intro k. replace (2 * k + 1) with (k + S k) by lia. rewrite fib_add. ring. Qed.

Lemma fib_two_k : forall k, fib (2 * k) = fib k * (2 * fib (S k) - fib k).
Proof.
  destruct k as [|k']; [reflexivity|].
  replace (2 * S k') with (S k' + S k') by lia.
  rewrite (fib_add k' (S k')). rewrite !(fib_SSn k').
  set (a := fib (S k')). set (b := fib k').
  replace (2 * (a + b) - a) with (a + 2 * b) by lia. ring.
Qed.

Fixpoint fastpair (fuel n : nat) : nat * nat :=
  match fuel with
  | 0 => (0, 1)
  | S f =>
      match n with
      | 0 => (0, 1)
      | S _ =>
          let (a, b) := fastpair f (n / 2) in
          let c := a * (2 * b - a) in
          let d := a * a + b * b in
          if n mod 2 =? 0 then (c, d) else (d, c + d)
      end
  end.

Theorem fast_fib : forall fuel n, n <= fuel -> fastpair fuel n = (fib n, fib (S n)).
Proof.
  induction fuel as [|f IH]; intros n Hn.
  - assert (n = 0) by lia. subst. reflexivity.
  - destruct n as [|n']; [reflexivity|]. cbn [fastpair].
    assert (Hlt : S n' / 2 < S n') by (apply Nat.div_lt; lia).
    rewrite (IH (S n' / 2)) by lia.
    set (k := S n' / 2) in *.
    pose proof (Nat.div_mod_eq (S n') 2) as Hdm.
    destruct (S n' mod 2 =? 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      assert (Hk : S n' = 2 * k) by lia.
      rewrite Hk. rewrite fib_two_k.
      replace (S (2 * k)) with (2 * k + 1) by lia. rewrite fib_two_kp1.
      reflexivity.
    + apply Nat.eqb_neq in Em.
      assert (Hmod : S n' mod 2 = 1) by (pose proof (Nat.mod_upper_bound (S n') 2); lia).
      assert (Hk : S n' = 2 * k + 1) by lia.
      rewrite Hk.
      replace (S (2 * k + 1)) with (S (S (2 * k))) by lia.
      rewrite fib_SSn. replace (S (2 * k)) with (2 * k + 1) by lia.
      rewrite fib_two_kp1, fib_two_k. f_equal; lia.
Qed.
