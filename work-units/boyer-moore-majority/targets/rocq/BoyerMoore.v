(* analysis@home — work unit: boyer-moore-majority (Rocq target).
 *
 * The Boyer-Moore majority vote (1981): find a strict majority element in ONE
 * left-to-right pass using O(1) extra space — just a candidate and a counter.
 *   step (c,0)      a = (a, 1)
 *   step (c, S k0)  a = if a = c then (c, S (S k0)) else (c, k0)
 * Correctness: if some m occurs in more than half the list (length l < 2*cnt m l)
 * then the final candidate is m:
 *   boyer_moore_majority : length l < 2 * cnt m l -> fst (bm l) = m.
 * The proof carries the cancellation invariant
 *   (A) forall x <> c, 2*cnt x l + k <= length l
 *   (B) 2*cnt c l <= length l + k
 * by induction over the processed prefix (rev_ind).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List.
Import ListNotations.

Fixpoint cnt (x:nat) (l:list nat) : nat :=
  match l with [] => 0 | y::ys => (if Nat.eq_dec x y then 1 else 0) + cnt x ys end.

Lemma cnt_app : forall x l m, cnt x (l ++ m) = cnt x l + cnt x m.
Proof. intros x l m; induction l as [|y ys IH]; simpl; [reflexivity|]; rewrite IH; lia. Qed.

Lemma cnt_snoc_eq : forall a l, cnt a (l ++ [a]) = S (cnt a l).
Proof. intros a l. rewrite cnt_app. cbn [cnt]. destruct (Nat.eq_dec a a); [lia|congruence]. Qed.

Lemma cnt_snoc_neq : forall x a l, x <> a -> cnt x (l ++ [a]) = cnt x l.
Proof. intros x a l Hxa. rewrite cnt_app. cbn [cnt]. destruct (Nat.eq_dec x a); [congruence|lia]. Qed.

Definition step (st:nat*nat) (a:nat) : nat*nat :=
  match st with
  | (c, 0)    => (a, 1)
  | (c, S k0) => if Nat.eq_dec a c then (c, S (S k0)) else (c, k0)
  end.

Definition bm (l:list nat) : nat*nat := fold_left step l (0,0).

Definition INV (l:list nat) (st:nat*nat) : Prop :=
  (forall x, x <> fst st -> 2 * cnt x l + snd st <= length l) /\
  2 * cnt (fst st) l <= length l + snd st.

Lemma bm_inv : forall l, INV l (fold_left step l (0,0)).
Proof.
  induction l as [|a l IHl] using rev_ind.
  - split; cbn [cnt fst snd length fold_left]; intros; lia.
  - rewrite fold_left_app. cbn [fold_left].
    destruct (fold_left step l (0,0)) as [c k].
    unfold INV in IHl. cbn [fst snd] in IHl. destruct IHl as [IA IB].
    destruct k as [|k0]; cbn [step].
    + (* k = 0 : restart, new state (a,1) *)
      split; cbn [fst snd].
      * intros x Hx. rewrite app_length; cbn [length].
        destruct (Nat.eq_dec x a) as [->|Hxa].
        -- now elim Hx.
        -- rewrite (cnt_snoc_neq x a l Hxa).
           destruct (Nat.eq_dec x c) as [->|Hxc]; [lia| specialize (IA x Hxc); lia].
      * rewrite app_length; cbn [length]. rewrite cnt_snoc_eq.
        destruct (Nat.eq_dec a c) as [->|Hac]; [lia| specialize (IA a Hac); lia].
    + destruct (Nat.eq_dec a c) as [e|Hac].
      * (* a = c : count up, state (c, S (S k0)) *)
        subst a. split; cbn [fst snd].
        -- intros x Hx. rewrite app_length; cbn [length].
           rewrite (cnt_snoc_neq x c l Hx). specialize (IA x Hx); lia.
        -- rewrite app_length; cbn [length]. rewrite cnt_snoc_eq. lia.
      * (* a <> c : count down, state (c, k0) *)
        split; cbn [fst snd].
        -- intros x Hx. rewrite app_length; cbn [length].
           destruct (Nat.eq_dec x a) as [->|Hxa].
           ++ rewrite cnt_snoc_eq. specialize (IA a Hx); lia.
           ++ rewrite (cnt_snoc_neq x a l Hxa). specialize (IA x Hx); lia.
        -- rewrite app_length; cbn [length].
           rewrite (cnt_snoc_neq c a l (fun h => Hac (eq_sym h))). lia.
Qed.

(* Boyer-Moore correctness: a strict majority element is found in one pass. *)
Theorem boyer_moore_majority : forall l m,
  length l < 2 * cnt m l -> fst (bm l) = m.
Proof.
  intros l m Hmaj. unfold bm.
  pose proof (bm_inv l) as H.
  destruct (fold_left step l (0,0)) as [c k].
  cbn [fst snd] in H |- *. destruct H as [IA IB].
  destruct (Nat.eq_dec c m) as [e|Hcm]; [exact e|].
  assert (Hmc : m <> c) by (intro He; apply Hcm; now subst).
  specialize (IA m Hmc). lia.
Qed.
