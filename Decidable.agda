module Decidable where

open import Data.Nat   using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
open import Data.Bool  using (Bool; true; false; if_then_else_; not)
open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)
open import Function   using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

1<2 : Dec (1 < 2)
1<2 = yes (s≤s (s≤s z≤n))

1≡1 : Dec (1 ≡ 1)
1≡1 = yes refl

1≡2 : Dec (1 ≡ 2)
1≡2 = no help -- alternative solution is `no λ ()'
  where
    help : ¬ (1 ≡ 2)
    help ()

1>2 : Dec (1 > 2)
1>2 = no help
  where
    help : ¬ (1 > 2)
    help (s≤s ())
