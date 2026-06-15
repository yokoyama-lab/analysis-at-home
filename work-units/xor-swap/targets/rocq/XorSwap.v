(* analysis@home — work unit: xor-swap (Rocq target).
 *
 * Swapping two values with XOR and NO temporary variable:
 *   a ^= b;  b ^= a;  a ^= b   (the three-XOR trick)
 * really does swap them. Captured as `xorswap a b = (b, a)`, proved purely from
 * XOR being commutative, associative and self-cancelling (x XOR x = 0).
 *
 * VERIFIED (Print Assumptions: closed under the global context). *)

Require Import Arith.

Definition xorswap (a b : nat) : nat * nat :=
  let a1 := Nat.lxor a b in        (* a ^= b *)
  let b1 := Nat.lxor b a1 in       (* b ^= a  (now b1 = a) *)
  let a2 := Nat.lxor a1 b1 in      (* a ^= b  (now a2 = b) *)
  (a2, b1).

Theorem xorswap_correct : forall a b, xorswap a b = (b, a).
Proof.
  intros a b. unfold xorswap; cbv zeta.
  assert (Hb : Nat.lxor b (Nat.lxor a b) = a).
  { rewrite (Nat.lxor_comm a b), <- Nat.lxor_assoc,
            Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity. }
  f_equal.
  - rewrite Hb, (Nat.lxor_comm (Nat.lxor a b) a), <- Nat.lxor_assoc,
            Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity.
  - exact Hb.
Qed.
