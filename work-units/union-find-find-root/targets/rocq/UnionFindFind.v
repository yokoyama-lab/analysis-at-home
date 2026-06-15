(* analysis@home — work unit: union-find-find-root (Rocq target). VERIFIED (Print
   Assumptions: closed under the global context). Under the invariant that parents
   point to a not-larger index, find terminates at a root (a fixed point). *)

Require Import List Arith Lia.
Import ListNotations.
(* Disjoint-set forest as a parent array p; root r has p[r]=r. find follows parents. *)
Fixpoint find (fuel : nat) (p : list nat) (x : nat) : nat :=
  match fuel with 0 => x | S f => let px := nth x p x in if px =? x then x else find f p px end.

(* Under the invariant "parents point to a not-larger index", find reaches a root. *)
Theorem find_reaches_root :
  forall fuel p x, (forall i, nth i p i <= i) -> x <= fuel ->
    nth (find fuel p x) p (find fuel p x) = find fuel p x.
Proof.
  induction fuel as [|f IH]; intros p x Hinv Hx; simpl.
  - assert (x = 0) by lia. subst. pose proof (Hinv 0). lia.
  - destruct (Nat.eqb_spec (nth x p x) x) as [Heq | Hneq].
    + exact Heq.
    + apply IH. exact Hinv. pose proof (Hinv x). lia.
Qed.
