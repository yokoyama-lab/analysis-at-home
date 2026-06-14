(* analysis@home — work unit: base-b-digit-count (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). A number below b^k has at most k base-b digits (= floor(log_b n)+1). *)

Require Import Arith Lia.

Lemma div_lt : forall a b c, 0 < b -> a < b * c -> a / b < c.
Proof. intros a b c Hb Hlt.
  pose proof (Nat.div_mod a b ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound a b ltac:(lia)) as Hm. nia. Qed.
Fixpoint ndigits (fuel b n : nat) : nat :=
  match fuel with 0 => 0 | S f => match n with 0 => 0 | _ => S (ndigits f b (n / b)) end end.
Theorem digit_count_bound : forall k b fuel n, 2 <= b -> n < b ^ k -> ndigits fuel b n <= k.
Proof.
  induction k as [|k' IHk]; intros b fuel n Hb Hn.
  - simpl in Hn. assert (n = 0) by lia. subst. destruct fuel; cbn [ndigits]; lia.
  - destruct fuel as [|f]. cbn [ndigits]. lia.
    destruct n as [|n']. cbn [ndigits]. lia.
    cbn [ndigits].
    assert (E : b ^ S k' = b * b ^ k') by reflexivity.
    assert (Hhalf : S n' / b < b ^ k') by (apply div_lt; lia).
    specialize (IHk b f (S n' / b) Hb Hhalf). lia. Qed.
