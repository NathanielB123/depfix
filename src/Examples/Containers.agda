{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Simple

module Examples.Containers where

record Con : Set₁ where
  constructor _▹_
  field
    Sh : Set
    Po : Sh → Set
open Con public

⟦_⟧ : Con → Set → Set
⟦ C ⟧ X = Σ (C .Sh) (λ s → (C .Po) s → X)

instance Con-Functor : ∀ {C : Con} → Functor ⟦ C ⟧
Con-Functor .All P (s , p) = ∀ x → P (p x)
Con-Functor .all P f (s , p) x = f (p x)
Con-Functor .replace (s , p) fp = s , fp

Con-Functor .fmap-comp f g (s , p) = refl
Con-Functor .fmap-id (s , p) = refl

W : Con → Set
W C = Fix (⟦_⟧ C)
