-- analysis@home — work unit: fast-exponentiation-mults (Agda target)
-- VERIFIED: `agda --safe` type-checks this (no postulate, no holes). Same
-- theorem as the Rocq/Lean/Isabelle targets: square-and-multiply uses
-- <= 2*(bits of exponent) multiplications. Uses agda-stdlib.

module Submission where

open import Data.Nat using (ℕ; zero; suc; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (*-suc; m≤n⇒m≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)

sqm : ℕ → List Bool → ℕ × ℕ
sqm sq [] = (1 , 0)
sqm sq (true ∷ r) =
  (sq * proj₁ (sqm (sq * sq) r) , suc (suc (proj₂ (sqm (sq * sq) r))))
sqm sq (false ∷ r) =
  (proj₁ (sqm (sq * sq) r) , suc (proj₂ (sqm (sq * sq) r)))

square_and_multiply_mults : ∀ sq ds → proj₂ (sqm sq ds) ≤ 2 * length ds
square_and_multiply_mults sq [] = z≤n
square_and_multiply_mults sq (true ∷ r) =
  subst (proj₂ (sqm sq (true ∷ r)) ≤_) (sym (*-suc 2 (length r)))
        (s≤s (s≤s (square_and_multiply_mults (sq * sq) r)))
square_and_multiply_mults sq (false ∷ r) =
  subst (proj₂ (sqm sq (false ∷ r)) ≤_) (sym (*-suc 2 (length r)))
        (m≤n⇒m≤1+n (s≤s (square_and_multiply_mults (sq * sq) r)))
