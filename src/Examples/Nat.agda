{-# OPTIONS --cubical-compatible --rewriting #-}

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong)
  renaming (trans to _∙_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Function using (_∘_; id)

open import Utils
open import Simple
open import SimpleUtils

module Examples.Nat where

NatD : Set → Set
NatD N = ⊤ + N

NatD-All : ∀ {A} (P : A → Set) → NatD A → Set
NatD-All P (inl tt) = ⊤
NatD-All P (inr x) = P x

instance NatD-Functor : Functor NatD

NatD-Functor .All = NatD-All
NatD-Functor .all P f (inl tt) = tt
NatD-Functor .all P f (inr x) = f x
NatD-Functor .collect (inl tt) tt = inl tt
NatD-Functor .collect (inr x) p = inr (x , p)
NatD-Functor .discard (inl tt) = inl tt
NatD-Functor .discard (inr (_ , y)) = inr y

NatD-Functor .discard-coh (inl tt) = refl
NatD-Functor .discard-coh (inr (_ , _)) = refl
NatD-Functor .collect-fst (inl tt) p = refl
NatD-Functor .collect-fst (inr x) p = refl
NatD-Functor .fmap-id (inl tt) = refl
NatD-Functor .fmap-id (inr _) = refl
NatD-Functor .fmap-comp f g (inl tt) = refl
NatD-Functor .fmap-comp f g (inr _) = refl

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
