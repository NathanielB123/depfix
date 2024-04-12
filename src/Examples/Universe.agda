{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import IndRec

module Examples.Universe where

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
