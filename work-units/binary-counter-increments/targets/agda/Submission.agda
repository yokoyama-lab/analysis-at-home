-- analysis@home — work unit: binary-counter-increments (Agda target)
-- VERIFIED: `agda --safe` type-checks this (no postulate, no holes). Same
-- theorem as the Rocq/Lean/Isabelle targets: n increments cost <= 2n bit flips
-- (amortized), via the potential = popcount. Uses agda-stdlib.

module Submission where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-suc; m≤m+n)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

count-ones : List Bool → ℕ
count-ones [] = 0
count-ones (true ∷ r) = suc (count-ones r)
count-ones (false ∷ r) = count-ones r

incr : List Bool → List Bool × ℕ
incr [] = (true ∷ [] , 1)
incr (false ∷ r) = (true ∷ r , 1)
incr (true ∷ r) = (false ∷ proj₁ (incr r) , suc (proj₂ (incr r)))

incr-n : ℕ → List Bool × ℕ
incr-n zero = ([] , 0)
incr-n (suc k) =
  (proj₁ (incr (proj₁ (incr-n k))) ,
   proj₂ (incr-n k) + proj₂ (incr (proj₁ (incr-n k))))

flips : ℕ → ℕ
flips n = proj₂ (incr-n n)

incr-flips : ∀ bs → proj₂ (incr bs) + count-ones (proj₁ (incr bs)) ≡ 2 + count-ones bs
incr-flips [] = refl
incr-flips (false ∷ r) = refl
incr-flips (true ∷ r) = cong suc (incr-flips r)

incr-n-invariant : ∀ n → proj₂ (incr-n n) + count-ones (proj₁ (incr-n n)) ≡ 2 * n
incr-n-invariant zero = refl
incr-n-invariant (suc k) =
  let a = proj₂ (incr-n k)
      b = proj₂ (incr (proj₁ (incr-n k)))
      cq = count-ones (proj₁ (incr (proj₁ (incr-n k))))
      cp = count-ones (proj₁ (incr-n k))
  in begin
    (a + b) + cq
      ≡⟨ +-assoc a b cq ⟩
    a + (b + cq)
      ≡⟨ cong (a +_) (incr-flips (proj₁ (incr-n k))) ⟩
    a + (2 + cp)
      ≡⟨ cong (a +_) (+-comm 2 cp) ⟩
    a + (cp + 2)
      ≡⟨ sym (+-assoc a cp 2) ⟩
    (a + cp) + 2
      ≡⟨ cong (_+ 2) (incr-n-invariant k) ⟩
    2 * k + 2
      ≡⟨ +-comm (2 * k) 2 ⟩
    2 + 2 * k
      ≡⟨ sym (*-suc 2 k) ⟩
    2 * suc k
  ∎

binary_counter_increments_amortized : ∀ n → flips n ≤ 2 * n
binary_counter_increments_amortized n =
  subst (flips n ≤_) (incr-n-invariant n)
        (m≤m+n (flips n) (count-ones (proj₁ (incr-n n))))
