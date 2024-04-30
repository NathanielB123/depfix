{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₂)
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

instance UD-Functor : Functor Set UD

UD-Functor .interpret = _⟦_⟧D
UD-Functor .All P (inl tt) = ⊤
UD-Functor .All P (inr (A , B)) = Σ (P A) (λ p → ∀ a → P (B a))
UD-Functor .all P p (inl tt) = tt
UD-Functor .all P p (inr (a , b)) = p a , (p ∘ b)
UD-Functor .collect (inl tt) tt = inl tt
UD-Functor .collect (inr (a , b)) (p , q) = inr ((a , p) , (λ ia → b ia , q ia))
UD-Functor .discard (inl tt) = inl tt
UD-Functor .discard (inr ((a , p) , b)) = inr (p , (proj₂ ∘ b))

UD-Functor .discard-coh (inl tt) = refl
UD-Functor .discard-coh (inr (_ , _)) = refl
UD-Functor .collect-fst (inl tt) _ = refl
UD-Functor .collect-fst (inr (_ , _)) _ = refl
UD-Functor .fmap-id (inl tt) = refl
UD-Functor .fmap-id (inr (_ , _)) = refl
UD-Functor .fmap-comp f g (inl tt) = refl
UD-Functor .fmap-comp f g (inr (_ , _)) = refl

U = Fix UD
⟦_⟧ : U → Set
⟦_⟧ = fixInterpret
