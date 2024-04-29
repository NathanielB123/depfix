{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (id; _∘_)

open import Utils

module IndRec where

record Functor (B : Set₁) (F : (A : Set) → (A → B) → Set) : Set₁ where
  field
    All     : ∀ {A i} (P : A → Set) → F A i → Set
    all     : ∀ {A i} (P : A → Set) (p : ∀ x → P x) (xs : F A i) → All P xs
    collect : ∀ {A B C} (xs : F A (λ _ → C)) → All (λ _ → B) xs 
            → F B (λ _ → C)
  
    identity    : ∀ {A B} (xs : F A (λ _ → B)) → xs ≡ collect _ (all _ id xs)
    composition : ∀ {A B C D} (f : A → B) (g : B → C) (xs : F A (λ _ → D)) 
                → collect _ (all _ g (collect _ (all _ f xs))) 
                ≡ collect _ (all _ (g ∘ f) xs)

    interpret : ∀ {A} r → F A r → B
open Functor ⦃...⦄ public

postulate
  Fix : ∀ {B} F → ⦃ Functor B F ⦄ → Set
  fixInterpret : ∀ {B F} → ⦃ _ : Functor B F ⦄ → Fix F → B
  fix : ∀ {B F} ⦃ _ : Functor B F ⦄ → F (Fix F) fixInterpret → Fix F
  fixInterpretβ : ∀ {B} {F} ⦃ _ : Functor B F ⦄ (a : F (Fix F) fixInterpret) 
                → fixInterpret (fix a) ≡ interpret fixInterpret a

  Fix-elim : ∀ {B} {F} ⦃ _ : Functor B F ⦄
               (P : Fix F → Set)
           → (∀ (d : F (Fix F) _) → All P d → P (fix d)) 
           → ∀ x → P x
  fixβ : ∀ {B} {F} ⦃ _ : Functor B F ⦄ 
           (P : Fix F → Set) 
           (m : ∀ (d : F (Fix F) _) → All P d → P (fix d)) d
       → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

{-# REWRITE fixInterpretβ fixβ #-}
