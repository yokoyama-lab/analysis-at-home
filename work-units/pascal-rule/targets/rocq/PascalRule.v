(* analysis@home — work unit: pascal-rule (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). C(n+1,k+1) = C(n,k) + C(n,k+1). *)

Require Import Arith Lia.

Fixpoint binom (n k:nat) := match n,k with _,0=>1 | 0,S _=>0 | S n',S k'=>binom n' k'+binom n' (S k') end.
Theorem binom_pascal : forall n k, binom (S n) (S k) = binom n k + binom n (S k).
Proof. reflexivity. Qed.
