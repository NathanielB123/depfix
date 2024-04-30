{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_) 
open import Function.Base using (id; _∘_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Utils

module Simple where

record Functor (F : Set → Set) : Set₁ where
  field
    All     : ∀ {A} (P : A → Set) → F A → Set
    all     : ∀ {A} (P : A → Set) (p : ∀ x → P x) xs → All P xs
    -- Thanks to Peio Borthelle on the Agda Zulip for suggesting this signature 
    -- for 'collect'!
    -- https://agda.zulipchat.com/#narrow/stream/238741-general/topic/Formalising.20Inductive.20Types/near/433118420
    collect : ∀ {A P} (xs : F A) (ps : All P xs) → F (Σ A P)
    discard : ∀ {A B} → F (Σ A (λ _ → B)) → F B

  -- Note that 'replace' is all that is needed to state the functor laws
  -- (i.e. splitting into 'collect' and 'discard' is overkill) but being able
  -- to collect 'All's with non-constant predicates seems useful
  replace : ∀ {A B} (xs : F A) (ps : All (λ _ → B) xs) → F B
  replace xs = discard ∘ collect xs

  fmap : ∀ {A B} → (A → B) → F A → F B
  fmap f xs = replace xs (all _ f xs)

  field
    discard-coh : ∀ {A B} (xs : F (A × B)) 
                → fmap proj₂ xs ≡ discard xs
    collect-fst : ∀ {A P} (xs : F A) (p : _) 
                → fmap proj₁ (collect xs (all P p xs)) ≡ xs
    fmap-id     : ∀ {A} (xs : F A) → fmap id xs ≡ xs
    fmap-comp   : ∀ {A B C} (f : A → B) (g : B → C) xs 
                → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs

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
