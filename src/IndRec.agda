{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)

open import Utils

module IndRec where

-- Core

record Functor (B : Set₁) (F : (A : Set) → (A → B) → Set) : Set₁ where
  field
    All     : ∀ {A i} (P : A → Set) → F A i → Set
    all     : ∀ {A i} (P : A → Set) (p : ∀ x → P x) (xs : F A i) → All P xs
    collect : ∀ {A B C} (xs : F A (λ _ → C)) → All (λ _ → B) xs 
            → F B (λ _ → C)
    
    identity : ∀ {A B} (xs : F A (λ _ → B)) → xs ≡ collect _ (all _ id xs)
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

-- Utils

fmap : ∀ {F} ⦃ _ : Functor Set F ⦄ {A B C} 
    → (A → B) → F A (λ _ → C) → F B (λ _ → C)
fmap f xs = collect xs (all _ f xs)

-- Example: Inductive-recursive universe containing ⊤ and Π types

UD : (u : Set) → (u → Set) → Set
UD u i = ⊤ + Σ u (λ a → i a → u)

_⟦_⟧D : ∀ {A} r → UD A r → Set
r ⟦ inl tt ⟧D = ⊤
r ⟦ inr (A , B) ⟧D = (a : r A) → r (B a)

UD-All : ∀ {u i} (P : u → Set) → UD u i → Set
UD-All P (inl tt) = ⊤
UD-All {i = i} P (inr (A , B)) 
  = Σ (P A) (λ p → (a : i A) → P (B a))

UD-all : ∀ {u i} (P : u → Set) (p : ∀ x → P x) (A : UD u i) → UD-All P A
UD-all P p (inl tt) = tt
UD-all P p (inr (a , b)) = p a , (p ∘ b)

UD-collect : ∀ {A B C} (xs : UD A (λ _ → C)) → UD-All (λ _ → B) xs 
            → UD B (λ _ → C)
UD-collect (inl tt) tt = inl tt
UD-collect (inr (a , b)) (p , q) = inr (p , q)

instance UD-Functor : Functor Set UD

UD-Functor .All = UD-All
UD-Functor .all = UD-all
UD-Functor .collect = UD-collect
UD-Functor .identity (inl tt) = refl
UD-Functor .identity (inr (a , b)) = refl
UD-Functor .composition f g (inl tt) = refl
UD-Functor .composition f g (inr (a , b)) = refl
UD-Functor .interpret = _⟦_⟧D

U = Fix UD
⟦_⟧ : U → Set
⟦_⟧ = fixInterpret
