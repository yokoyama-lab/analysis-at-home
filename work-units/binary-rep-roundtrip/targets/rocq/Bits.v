(* analysis@home — work unit: binary-rep-roundtrip (Rocq target).
 *
 * The binary representation of a natural number is faithful: writing n out in
 * base 2 (least-significant bit first) and reading it back recovers n.
 *   to_bits n  = (n mod 2) :: to_bits (n / 2)     (bits are 0/1)
 *   from_bits  = Horner in base 2
 *   bits_roundtrip : n <= fuel -> from_bits (to_bits fuel n) = n.
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith Lia List.
Import ListNotations.

Fixpoint to_bits (fuel n : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => match n with 0 => [] | S _ => (n mod 2) :: to_bits f (n / 2) end
  end.

Fixpoint from_bits (l : list nat) : nat :=
  match l with [] => 0 | b :: t => b + 2 * from_bits t end.

Theorem bits_roundtrip : forall fuel n, n <= fuel -> from_bits (to_bits fuel n) = n.
Proof.
  induction fuel as [|f IH]; intros n Hn.
  - assert (n = 0) by lia. subst. reflexivity.
  - destruct n as [|n']; [reflexivity|]. cbn [to_bits].
    assert (Hlt : S n' / 2 < S n') by (apply Nat.div_lt; lia).
    cbn [from_bits]. rewrite (IH (S n' / 2)) by lia.
    pose proof (Nat.div_mod_eq (S n') 2). lia.
Qed.
