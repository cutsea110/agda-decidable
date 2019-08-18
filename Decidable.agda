module Decidable where

open import Data.Nat   using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_; _≮_; _≯_)
open import Data.Bool  using (Bool; true; false; if_then_else_; not)
open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function   using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym)

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
    help : 1 ≢ 2
    help ()

1>2 : Dec (1 > 2)
1>2 = no help
  where
    help : 1 ≯ 2
    help (s≤s ())

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero ≟ zero = yes refl
zero ≟ suc b = no (λ ())
suc a ≟ zero = no (λ ())
suc a ≟ suc b with a ≟ b
(suc a ≟ suc b) | yes a≡b = yes (cong suc a≡b)
(suc a ≟ suc b) | no  a≢b  = no (help a b a≢b)
  where
    help : ∀ a b → a ≢ b → suc a ≢ suc b
    help a .a prf refl = prf refl

_≤?_ : (a b : ℕ) → Dec (a ≤ b)
zero ≤? b = yes z≤n
suc a ≤? zero = no (λ ())
suc a ≤? suc b with a ≤? b
(suc a ≤? suc b) | yes a≤b = yes (s≤s a≤b)
(suc a ≤? suc b) | no  a≰b = no (help a b a≰b)
  where
    help : ∀ a b → ¬ (a ≤ b) → ¬ (suc a ≤ suc b)
    help a b a≰b (s≤s p) = a≰b p

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false
