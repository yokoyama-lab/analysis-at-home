(* analysis@home — work unit: union-find-path-compression (Rocq target). VERIFIED
   (Print Assumptions: closed under the global context). After path compression
   (point x directly to its root), find reaches the root in ONE step. *)

Require Import List Arith Lia.
Import ListNotations.
Fixpoint find (fuel : nat) (p : list nat) (x : nat) : nat :=
  match fuel with 0 => x | S f => let px := nth x p x in if px =? x then x else find f p px end.
(* update p[i] := v *)
Fixpoint upd (p : list nat) (i v : nat) : list nat :=
  match p, i with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S j => h :: upd t j v
  end.
Lemma nth_upd_eq : forall p i v d, i < length p -> nth i (upd p i v) d = v.
Proof. induction p as [|h t IH]; intros i v d Hi; simpl in *.
  - lia.
  - destruct i as [|j]; simpl. reflexivity. apply IH. lia. Qed.

(* After path compression (point x directly to its root r), find reaches the root
   in ONE step -- the mechanism by which path compression accelerates find. *)
Theorem path_compression_one_step :
  forall p x r, x < length p -> find 1 (upd p x r) x = r.
Proof.
  intros p x r Hx. simpl. rewrite nth_upd_eq by exact Hx.
  destruct (Nat.eqb_spec r x). subst. reflexivity. reflexivity.
Qed.
