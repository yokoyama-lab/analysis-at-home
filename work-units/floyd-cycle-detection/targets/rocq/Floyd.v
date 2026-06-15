(* analysis@home — work unit: floyd-cycle-detection (Rocq target).
 *
 * Floyd's "tortoise and hare": detect a cycle in the orbit x, f(x), f(f(x)), ...
 * with O(1) memory — two pointers, one moving twice as fast. The surprising
 * claim is that they MEET: whenever the orbit ever repeats a value (which it
 * must, by pigeonhole, for any f with a finite reachable set), there is a step
 * m >= 1 at which the tortoise (m steps) and the hare (2m steps) coincide:
 *   floyd_meeting : i < j -> iter f i x = iter f j x ->
 *                   exists m, 1 <= m /\ iter f m x = iter f (2*m) x.
 * No record of visited states is kept — only the two moving pointers.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

Fixpoint iter (f : nat -> nat) (n x : nat) : nat :=
  match n with 0 => x | S k => f (iter f k x) end.

Lemma iter_add : forall f a b x, iter f (a + b) x = iter f a (iter f b x).
Proof.
  intros f a b x. induction a as [|a IH]; simpl; [reflexivity | now rewrite IH].
Qed.

(* Once the orbit repeats (index i = index j), it is periodic with period j-i
   from index i onward. *)
Lemma periodic : forall f x i j, iter f i x = iter f j x -> i <= j ->
  forall k, i <= k -> iter f ((j - i) + k) x = iter f k x.
Proof.
  intros f x i j Hc Hij k Hk. induction Hk as [|m Hm IH].
  - rewrite Nat.sub_add by exact Hij. now symmetry.
  - replace (j - i + S m) with (S (j - i + m)) by lia. simpl. now rewrite IH.
Qed.

(* ... hence periodic with any multiple of the period. *)
Lemma multiperiod : forall f x i j, iter f i x = iter f j x -> i <= j ->
  forall t k, i <= k -> iter f (t * (j - i) + k) x = iter f k x.
Proof.
  intros f x i j Hc Hij t. induction t as [|t IH]; intros k Hk.
  - reflexivity.
  - replace (S t * (j - i) + k) with ((j - i) + (t * (j - i) + k)) by lia.
    rewrite (periodic f x i j Hc Hij (t * (j - i) + k) ltac:(nia)).
    apply IH; exact Hk.
Qed.

(* Tortoise (m steps) and hare (2m steps) coincide for some m >= 1. *)
Theorem floyd_meeting : forall f x i j, i < j -> iter f i x = iter f j x ->
  exists m, 1 <= m /\ iter f m x = iter f (2 * m) x.
Proof.
  intros f x i j Hlt Hc.
  exists ((i + 1) * (j - i)). split.
  - nia.
  - pose proof (multiperiod f x i j Hc ltac:(lia) (i + 1)
                  ((i + 1) * (j - i)) ltac:(nia)) as H.
    replace (2 * ((i + 1) * (j - i)))
      with ((i + 1) * (j - i) + (i + 1) * (j - i)) by lia.
    symmetry. exact H.
Qed.
