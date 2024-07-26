{-# OPTIONS --cubical-compatible --rewriting #-}

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong)
  renaming (trans to _∙_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Function using (_∘_; id)
open import Level using (Level; Lift; lift)

open import Utils
open import Simple
open import SimpleUtils

module Examples.Nat where

NatD : Set → Set
NatD N = ⊤ + N

pattern zero = inl tt
pattern suc n = inr n

instance NatD-Functor : Functor NatD

NatD-Functor .All P zero = Lift _ ⊤
NatD-Functor .All P (suc x) = P x
NatD-Functor .all P f zero = lift tt
NatD-Functor .all P f (suc x) = f x
NatD-Functor .replace zero (lift tt) = zero
NatD-Functor .replace (suc x) y = suc y

NatD-Functor .fmap-comp f g zero = refl
NatD-Functor .fmap-comp f g (suc _) = refl
NatD-Functor .fmap-id zero = refl
NatD-Functor .fmap-id (suc _) = refl

Nat = Fix NatD

fzero : Nat
fzero = fix zero

fsuc : Nat → Nat
fsuc  = fix ∘ suc

add : Nat → Nat → Nat
add x y = Fix-fold (λ where zero → y; (suc x) → fsuc x) x

add-zero = Fix-elim _ (λ where zero (lift tt) → refl; (suc y) → cong fsuc)

add-suc : ∀ x y → fsuc (add x y) ≡ add x (fsuc y)
add-suc x y = Fix-elim (λ z → fsuc (add z y) ≡ add z (fsuc y)) 
                       (λ where zero (lift tt) → refl; (suc y) → cong fsuc) x

add-commutes : ∀ x y → add x y ≡ add y x
add-commutes x y 
  = Fix-elim (λ z → add z y ≡ add y z) 
              (λ where 
                zero (lift tt) → add-zero y
                (suc z) p → cong fsuc p ∙ add-suc y z) x
