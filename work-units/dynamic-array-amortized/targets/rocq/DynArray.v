(* analysis@home — work unit: dynamic-array-amortized (Rocq target).
 *
 * A dynamic array (table doubling) supports push in amortized O(1) (CLRS §17.4 /
 * TAOCP-adjacent). Each push writes one element (cost 1); when the array is full
 * (size = capacity) it first copies all `capacity` elements into an array of
 * double capacity. `da_cost n s c` is the total cost of `n` pushes starting at
 * size `s`, capacity `c`. The potential method (Phi = 2*size - capacity) gives a
 * constant amortized cost 3:
 *   da_cost n 0 1 <= 3 * n          (dynamic_array_amortized)
 * so the worst-case O(n) copy is paid for by the cheap pushes before it — O(1)
 * amortized. The crux is the geometric series 1+2+4+...+2^k < 2^(k+1).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia.

(* n pushes, current size s, capacity c. A push costs 1; if s = c it also copies
   the c existing elements and doubles the capacity. *)
Fixpoint da_cost (n s c : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => if s =? c
            then (1 + c) + da_cost n' (S s) (2 * c)
            else 1 + da_cost n' (S s) c
  end.

(* Potential-method invariant: with c >= 1 and c/2 <= s <= c, the actual cost
   plus the final potential is bounded by 3 per push. *)
Lemma da_cost_amortized : forall n s c,
  1 <= c -> s <= c -> c <= 2 * s + 1 -> da_cost n s c + c <= 3 * n + 2 * s + 1.
Proof.
  induction n as [|n' IH]; intros s c Hc Hsc Hub.
  - cbn [da_cost]. lia.
  - cbn [da_cost]. destruct (s =? c) eqn:E.
    + apply Nat.eqb_eq in E. subst c.
      specialize (IH (S s) (2 * s) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
    + apply Nat.eqb_neq in E.
      specialize (IH (S s) c ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* Amortized O(1): n pushes into a fresh array (size 0, capacity 1) cost <= 3n. *)
Theorem dynamic_array_amortized : forall n, da_cost n 0 1 <= 3 * n.
Proof. intro n. pose proof (da_cost_amortized n 0 1 ltac:(lia) ltac:(lia) ltac:(lia)). lia. Qed.
