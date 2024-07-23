{-# OPTIONS --cubical-compatible --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; proj₁)
open import Function using (_∘_)

open import IndexedIndRec

module IndexedIndRecUtils where

-- Utils

open import Relation.Binary.PropositionalEquality using (refl)

-- A RecFunctor with interpret defined on the whole domain of M can be
-- immediately turned into a Functor
RecFunctor→Functor : ∀ {I M F} → ⦃ PreFunctor I M F ⦄ → ⦃ RecFunctor I M M F ⦄ 
                   → Functor I M F
RecFunctor→Functor .prefunc = _
RecFunctor→Functor .fixInterpret = fixInterpretRec

fix-unfix-id : ∀ {I M F i} ⦃ _ : Functor I M F ⦄ (xs : Fix F i) 
              → fix (unfix xs) ≡ xs
fix-unfix-id xs = Fix-elim (λ _ xs → fix (unfix xs) ≡ xs) (λ _ _ → refl) xs

-- Catamorphisms for inductive-recursive/inductive-inductive functors are tricky 
-- (what should the interpret function be?), but paramorphisms come out nicely!
Fix-fold : ∀ {I M F A} ⦃ _ : Functor I M F ⦄ 
         → (∀ {i} → F (λ i → Fix F i × A) (λ i → fixInterpret i ∘ proj₁) i → A)
         → ∀ {i} → Fix F i → A
Fix-fold f xs = Fix-elim _ (λ d p → f (collect d p)) xs
