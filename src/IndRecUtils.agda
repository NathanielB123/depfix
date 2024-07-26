{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; cong; sym)
  renaming (trans to infixr 5 _∙_)

open import IndRec

module IndRecUtils where

module _ {M F} ⦃ _ : Functor M F ⦄ where

  unfix : Fix F → F (Fix F) fixInterpret
  unfix = Fix-elim _ (λ d _ → d)

  -- Catamorphisms for inductive-recursive functors are tricky (what should the 
  -- interpret function be?), but paramorphisms come out nicely!
  Fix-fold : ∀ {A} → (F (Fix F × A) (fixInterpret ∘ proj₁) → A) → Fix F → A
  Fix-fold f xs
    = Fix-elim _ (λ d p → f (collect d p)) xs

  collect-fst : ∀ {A P i} (xs : F A (λ _ → i)) p 
              → fmap proj₁ (collect xs (all P p xs)) ≡ xs
  collect-fst xs p = cong (fmap proj₁) (sym (collect-pairs xs p)) 
                   ∙ fmap-comp (λ x → x , p x) proj₁ xs ∙ fmap-id xs

  collect-snd : ∀ {A i} (xs : F A (λ _ → i))
              → fmap proj₂ (collect xs (all _ id xs)) ≡ xs
  collect-snd xs = discard-coh (collect xs (all _ id xs)) ∙ fmap-id xs
