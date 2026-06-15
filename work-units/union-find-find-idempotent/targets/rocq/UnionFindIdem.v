(* analysis@home — work unit: union-find-find-idempotent (Rocq target). VERIFIED
   (Print Assumptions: closed under the global context). find returns a stable
   representative: find (find x) = find x (the correctness property of union-find). *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint find (fuel : nat) (p : list nat) (x : nat) : nat :=
  match fuel with 0 => x | S f => let px := nth x p x in if px =? x then x else find f p px end.
Theorem find_reaches_root :
  forall fuel p x, (forall i, nth i p i <= i) -> x <= fuel ->
    nth (find fuel p x) p (find fuel p x) = find fuel p x.
Proof. induction fuel as [|f IH]; intros p x Hinv Hx; simpl.
  - assert (x = 0) by lia. subst. pose proof (Hinv 0). lia.
  - destruct (Nat.eqb_spec (nth x p x) x) as [Heq | Hneq].
    + exact Heq.
    + apply IH. exact Hinv. pose proof (Hinv x). lia. Qed.
Lemma find_of_root : forall fuel p r, nth r p r = r -> find fuel p r = r.
Proof. intros fuel p r H. destruct fuel; simpl. reflexivity. rewrite H, Nat.eqb_refl. reflexivity. Qed.
(* find returns a STABLE representative: find (find x) = find x. *)
Theorem find_idempotent :
  forall fuel p x, (forall i, nth i p i <= i) -> x <= fuel ->
    find fuel p (find fuel p x) = find fuel p x.
Proof.
  intros fuel p x Hinv Hx. apply find_of_root.
  apply find_reaches_root. exact Hinv. exact Hx.
Qed.
