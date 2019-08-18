module Decidable where

open import Data.Nat hiding (_≤_)
open import Relation.Nullary using (¬_)
open import Data.Empty

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

4≰2 : ¬ (4 ≤ 2)
4≰2 (s≤s (s≤s ()))
