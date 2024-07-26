{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_; 0ℓ; suc; Setω)

open import Utils

module Indexed where

variable
  Pℓ : Level

record Functor (I : Set) (F : (I → Set) → I → Set) 
             : Setω where
  field
    All     : ∀ {A} (P : ∀ i → A i → Set Pℓ) {i} → F A i → Set Pℓ
    all     : ∀ {A} (P : ∀ i → A i → Set Pℓ) (p : ∀ {i} x → P i x) {i} 
                (xs : F A i) 
            → All P xs
    collect : ∀ {A P i} (xs : F A i) → All P xs → F (λ i → Σ (A i) (P i)) i
    discard : ∀ {A B : I → Set} {i} → F (λ i → A i × B i) i → F B i
  
  replace : ∀ {A B i} (xs : F A i) → All (λ i _ → B i) xs → F B i
  replace xs ps = discard (collect xs ps)

  fmap : ∀ {A B i} → (∀ {i} → A i → B i) → F A i → F B i
  fmap f xs = replace xs (all _ f xs)

  field
    discard-coh : ∀ {A B : I → Set} {i} (xs : F (λ i → A i × B i) i) 
                → fmap proj₂ xs ≡ discard xs
    collect-fst : ∀ {A P i} (xs : F A i) (p : ∀ {i} x → P i x) 
                → fmap proj₁ (collect xs (all P p xs)) ≡ xs
    fmap-id     : ∀ {A i} (xs : F A i) → fmap id xs ≡ xs
    fmap-comp   : ∀ {A B C : I → Set} {i} 
                    (f : ∀ {i} → A i → B i) (g : ∀ {i} → B i → C i) (xs : F A i) 
                → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs

open Functor ⦃...⦄ public

postulate
  Fix : ∀ {I} F → ⦃ Functor I F ⦄ → I → Set
  fix : ∀ {I F i} ⦃ _ : Functor I F ⦄ → F (Fix F) i → Fix F i
  Fix-elim : ∀ {I F} ⦃ _ : Functor I F ⦄ (P : ∀ i → Fix F i → Set Pℓ)
            → (∀ {i} (d : F (Fix F) i) → All P d → P i (fix d)) 
            → ∀ {i} (x : Fix F i) → P i x
  fixβ : ∀ {I F} ⦃ _ : Functor I F ⦄ (P : ∀ i → Fix F i → Set Pℓ)
           (m : ∀ {i} → (d : F (Fix F) i) → All P d → P i (fix d)) {i} 
           (d : F (Fix F) i) 
       → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

{-# REWRITE fixβ #-}
  