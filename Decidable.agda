module Decidable where

open import Data.Nat hiding (_≤_)
open import Relation.Nullary using (¬_)
open import Data.Empty

open import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)
open PropEq.≡-Reasoning

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

4≰2 : ¬ (4 ≤ 2)
4≰2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

2≤ᵇ4 : (2 ≤ᵇ 4) ≡ true
2≤ᵇ4 =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

4≰ᵇ2 : (4 ≤ᵇ 2) ≡ false
4≰ᵇ2 =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
