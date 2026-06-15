(* analysis@home — work unit: binary-increment-correct (Rocq target).
 *
 * Incrementing a little-endian binary counter adds exactly one. `inc` ripples
 * the carry: a 0 bit flips to 1 and stops; a 1 bit flips to 0 and carries on.
 * Reading the bits back (Horner base 2):
 *   inc_correct : from_bits (inc l) = S (from_bits l).
 * This is the CORRECTNESS companion to `binary-counter-increments` (its amortized
 * O(1) cost).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List.
Import ListNotations.

Fixpoint from_bits (l : list bool) : nat :=
  match l with [] => 0 | b :: t => (if b then 1 else 0) + 2 * from_bits t end.

Fixpoint inc (l : list bool) : list bool :=
  match l with
  | [] => [true]
  | b :: t => if b then false :: inc t else true :: t
  end.

Theorem inc_correct : forall l, from_bits (inc l) = S (from_bits l).
Proof.
  induction l as [|b t IH]; [reflexivity|]. cbn [inc].
  destruct b; cbn [from_bits]; [rewrite IH | ]; lia.
Qed.
