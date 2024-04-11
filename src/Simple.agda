{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  renaming (trans to _∙_)
open import Function.Base using (id; _∘_)

open import Utils

module Simple where

-- Core

record Functor (F : Set → Set) : Set₁ where
  field
    All         : ∀ {A} (P : A → Set) → F A → Set
    all         : ∀ {A} (P : A → Set) (p : ∀ x → P x) xs → All P xs
    collect     : ∀ {A B} (xs : F A) → All (λ _ → B) xs → F B
    identity    : ∀ {A} (xs : F A) → xs ≡ collect xs (all _ id xs)
    composition : ∀ {A B C} (f : A → B) (g : B → C) xs 
                → collect _ (all _ g (collect _ (all _ f xs))) 
                ≡ collect _ (all _ (g ∘ f) xs)
open Functor ⦃...⦄

postulate
  Fix : ∀ (F : Set → Set) → ⦃ Functor F ⦄ → Set
  fix : ∀ {F : Set → Set} ⦃ _ : Functor F ⦄ → F (Fix F) → Fix F
  Fix-elim : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set) 
            → ((d : F (Fix F)) → All P d → P (fix d)) → ∀ x → P x
  fixβ : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set) 
            (m : (d : F (Fix F)) → All P d → P (fix d)) d 
        → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

{-# REWRITE fixβ #-}

-- Utils

fmap : ∀ {F : Set → Set} {A B : Set} → ⦃ Functor F ⦄ → (A → B) → F A → F B
fmap {F} {A} {B} f xs = collect _ (all _ f xs) 

Fix-fold : ∀ {F} {A : Set} ⦃ _ : Functor F ⦄ → (F A → A) → Fix F → A
Fix-fold {F} {A} f xs 
  = Fix-elim _ (λ d ps → f (collect _ ps)) xs

unfix : ∀ {F : Set → Set} ⦃ _ : Functor F ⦄ → Fix F → F (Fix F)
unfix xs = Fix-fold (fmap fix) xs

-- Example: Natural Numbers

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
