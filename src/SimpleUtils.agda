{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Product using (proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_)
  renaming (trans to _∙_)

open import Simple

module SimpleUtils where

collect-snd : ∀ {F A} ⦃ _ : Functor F ⦄ (xs : F A)
            → fmap proj₂ (collect xs (all _ id xs)) ≡ xs
collect-snd xs = discard-coh (collect xs (all _ id xs)) ∙ fmap-id xs

Fix-fold : ∀ {F A} ⦃ _ : Functor F ⦄ → (F A → A) → Fix F → A
Fix-fold f xs 
  = Fix-elim _ (λ d ps → f (replace _ ps)) xs

unfix : ∀ {F} ⦃ _ : Functor F ⦄ → Fix F → F (Fix F)
unfix xs = Fix-fold (fmap fix) xs
