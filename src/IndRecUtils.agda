{-# OPTIONS --cubical-compatible --rewriting #-}

open import IndRec

module IndRecUtils where

unfix : ∀ {B F} ⦃ _ : Functor B F ⦄ → Fix F → F (Fix F) fixInterpret
unfix = Fix-elim _ (λ d _ → d)

record Foldable (B : Set₁) (F : (A : Set) → (A → B) → Set) : Set₁ where
  field
    ⦃ functor ⦄ : Functor B F
    fold-interpret : F (Fix F) fixInterpret → B
    collect-fix : ∀ {A} (xs : F (Fix F) fixInterpret) → All (λ _ → A) xs 
                → F A (λ _ → fold-interpret xs)
open Foldable ⦃...⦄ public
  
Fix-fold : ∀ {B F A} ⦃ _ : Foldable B F ⦄ → (∀ {i} → F A i → A)
         → Fix F → A
Fix-fold {B} {F} {A} f xs = Fix-elim _ (λ d p → f (collect-fix d p)) xs
