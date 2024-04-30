{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id; _∘_)
open import Data.Product using (Σ; _×_; proj₁; proj₂)

open import Utils

module IndRec where

record Functor (M : Set₁) (F : (A : Set) → (A → M) → Set) : Set₁ where
  field
    interpret : ∀ {A} r → F A r → M

    All     : ∀ {A i} (P : A → Set) → F A i → Set
    all     : ∀ {A i} (P : A → Set) (p : ∀ x → P x) (xs : F A i) → All P xs

    collect : ∀ {A P i} (xs : F A i) → All P xs → F (Σ A P) (i ∘ proj₁)
    discard : ∀ {A B i} → F (Σ A (λ _ → B)) (i ∘ proj₂) → F B i

  fmap : ∀ {A B i} → (A → B) → F A (λ _ → i) → F B (λ _ → i)
  fmap f xs = discard (collect xs (all _ f xs))

  field
    -- Note that none of these laws cover non-trivial interpreting functions...
    -- Stronger ones might be possible
    discard-coh : ∀ {A B i} (xs : F (A × B) (λ _ → i)) 
                → fmap proj₂ xs ≡ discard xs
    collect-fst : ∀ {A P i} (xs : F A (λ _ → i)) (p : _) 
                → fmap proj₁ (collect xs (all P p xs)) ≡ xs
    fmap-id     : ∀ {A i} (xs : F A (λ _ → i)) → fmap id xs ≡ xs
    fmap-comp   : ∀ {A B C i} (f : A → B) (g : B → C) (xs : F A (λ _ → i)) 
                → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs

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
