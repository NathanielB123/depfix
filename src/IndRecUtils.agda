{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Product using (_×_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_)
  renaming (trans to _∙_)

open import IndRec

module IndRecUtils where

unfix : ∀ {M F} ⦃ _ : Functor M F ⦄ → Fix F → F (Fix F) fixInterpret
unfix = Fix-elim _ (λ d _ → d)

-- Catamorphisms for inductive-recursive functors are tricky (what should the 
-- interpret function be?), but paramorphisms come out nicely!
Fix-fold : ∀ {M F A} ⦃ _ : Functor M F ⦄ 
         → (F (Fix F × A) (fixInterpret ∘ proj₁) → A)
         → Fix F → A
Fix-fold {F = F} f xs
  = Fix-elim _ (λ d p → f (collect d p)) xs

collect-snd : ∀ {M F A i} ⦃ _ : Functor M F ⦄ (xs : F A (λ _ → i))
            → fmap proj₂ (collect xs (all _ id xs)) ≡ xs
collect-snd xs = discard-coh (collect xs (all _ id xs)) ∙ fmap-id xs
