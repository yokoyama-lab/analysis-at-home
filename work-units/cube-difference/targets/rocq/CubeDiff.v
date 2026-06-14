(* analysis@home — work unit: cube-difference (Rocq target). VERIFIED (Print Assumptions:
   closed under the global context). Consecutive cubes differ by 3n^2+3n+1. *)

Require Import Arith Lia.

Theorem cube_difference : forall n, (S n) * (S n) * (S n) = n * n * n + (3 * n * n + 3 * n + 1).
Proof. intro n. nia. Qed.
