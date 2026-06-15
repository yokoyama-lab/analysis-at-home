(* analysis@home — work unit: run-length-encoding (Rocq target).
 *
 * Run-length encoding is LOSSLESS: decoding the encoding returns the original
 * list. `encode` collapses maximal runs of equal elements into (value, count)
 * pairs; `decode` expands them back with `repeat`. The round-trip law
 *   rle_roundtrip : decode (encode l) = l
 * is the correctness statement every compressor must satisfy.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith List.
Import ListNotations.

Fixpoint encode (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | x :: xs =>
      match encode xs with
      | (y, c) :: rest => if x =? y then (y, S c) :: rest else (x, 1) :: (y, c) :: rest
      | [] => [(x, 1)]
      end
  end.

Fixpoint decode (l : list (nat * nat)) : list nat :=
  match l with [] => [] | (x, c) :: rest => repeat x c ++ decode rest end.

Theorem rle_roundtrip : forall l, decode (encode l) = l.
Proof.
  induction l as [|x xs IH]; [reflexivity|]. cbn [encode].
  destruct (encode xs) as [|[y c] rest] eqn:E.
  - cbn [decode] in IH. subst xs. reflexivity.
  - destruct (x =? y) eqn:Exy.
    + apply Nat.eqb_eq in Exy; subst y.
      cbn [decode repeat app]. f_equal. rewrite <- IH. cbn [decode]. reflexivity.
    + cbn [decode repeat app]. f_equal. exact IH.
Qed.
