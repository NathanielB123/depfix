{-# OPTIONS --cubical-compatible --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  renaming (trans to _∙_)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_∘_; id)

open import Utils
open import Simple
open import SimpleUtils

module Examples.Nat where

NatD : Set → Set
NatD N = ⊤ + N

NatD-All : ∀ {A} (P : A → Set) → NatD A → Set
NatD-All P (inl tt) = ⊤
NatD-All P (inr x) = P x

instance
  NatD-Functor : Functor NatD

NatD-identity : ∀ {A} (xs : NatD A) → xs ≡ fmap id xs
NatD-composition : ∀ {A B C} (f : A → B) (g : B → C) (xs : NatD A)
                  → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs

NatD-Functor .All = NatD-All
NatD-Functor .all P f (inl tt) = tt
NatD-Functor .all P f (inr x) = f x
NatD-Functor .collect (inl tt) tt = inl tt
NatD-Functor .collect (inr x) p = inr p
NatD-Functor .identity = NatD-identity
NatD-Functor .composition = NatD-composition

NatD-identity (inl tt) = refl
NatD-identity (inr x) = refl

NatD-composition _ _ (inl tt) = refl
NatD-composition _ _ (inr x) = refl

Nat = Fix NatD

zero : Nat
zero = fix (inl tt)

suc : Nat → Nat
suc = fix ∘ inr

add : Nat → Nat → Nat
add x y = Fix-fold (λ where (inl tt) → y; (inr x) → fix (inr x)) x

add-zero : ∀ x → x ≡ add x zero
add-zero = Fix-elim _ (λ where (inl tt) tt → refl; (inr y) → cong suc)

add-suc : ∀ x y → suc (add x y) ≡ add x (suc y)
add-suc x y = Fix-elim (λ z → suc (add z y) ≡ add z (suc y)) 
                        (λ where (inl tt) tt → refl; (inr y) → cong suc) x

add-commutes : ∀ x y → add x y ≡ add y x
add-commutes x y 
  = Fix-elim (λ z → add z y ≡ add y z) 
              (λ where 
                (inl tt) tt → add-zero y
                (inr z) p → cong suc p ∙ add-suc y z) x
