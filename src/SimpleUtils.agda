{-# OPTIONS --cubical-compatible --rewriting --local-confluence-check #-}

open import Data.Product using (proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong)
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
unfix = Fix-elim _ (λ xs _ → xs)

-- We cannot turn this into a definitional rewrite without losing confluence due
-- to how Fix-elim must block on expecting "fix d"
-- e.g. consider 
-- > Fix-elim _ _ (fix (unfix xs))
-- - If we don't cancel the adjacent fix-unfix, then we are able to apply fixβ.
-- - If we do cancel the adjacent fix-unfix, then we are left with a stuck term
--   headed by Fix-elim.
fix-unfix-id : ∀ {F} ⦃ _ : Functor F ⦄ (xs : Fix F) 
           → fix (unfix xs) ≡ xs
fix-unfix-id = Fix-elim (λ xs → fix (unfix xs) ≡ xs) 
                        (λ xs _ → refl)
