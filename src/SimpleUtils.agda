{-# OPTIONS --cubical-compatible --rewriting #-}

open import Simple

module SimpleUtils where

fmap : ∀ {F : Set → Set} {A B : Set} → ⦃ Functor F ⦄ → (A → B) → F A → F B
fmap {F} {A} {B} f xs = collect _ (all _ f xs) 

Fix-fold : ∀ {F} {A : Set} ⦃ _ : Functor F ⦄ → (F A → A) → Fix F → A
Fix-fold {F} {A} f xs 
  = Fix-elim _ (λ d ps → f (collect _ ps)) xs

unfix : ∀ {F : Set → Set} ⦃ _ : Functor F ⦄ → Fix F → F (Fix F)
unfix xs = Fix-fold (fmap fix) xs
