{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (id; _∘_)

open import Utils

module Simple where

record Functor (F : Set → Set) : Set₁ where
  field
    All         : ∀ {A} (P : A → Set) → F A → Set
    all         : ∀ {A} (P : A → Set) (p : ∀ x → P x) xs → All P xs
    collect     : ∀ {A B} (xs : F A) → All (λ _ → B) xs → F B
    identity    : ∀ {A} (xs : F A) → xs ≡ collect xs (all _ id xs)
    composition : ∀ {A B C} (f : A → B) (g : B → C) xs 
                → collect _ (all _ g (collect _ (all _ f xs))) 
                ≡ collect _ (all _ (g ∘ f) xs)
open Functor ⦃...⦄ public

postulate
  Fix : ∀ (F : Set → Set) → ⦃ Functor F ⦄ → Set
  fix : ∀ {F : Set → Set} ⦃ _ : Functor F ⦄ → F (Fix F) → Fix F
  Fix-elim : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set) 
            → ((d : F (Fix F)) → All P d → P (fix d)) → ∀ x → P x
  fixβ : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set) 
            (m : (d : F (Fix F)) → All P d → P (fix d)) d 
        → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

{-# REWRITE fixβ #-}
