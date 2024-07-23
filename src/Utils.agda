{-# OPTIONS --cubical-compatible #-}

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Utils where

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A + B
  inr : B → A + B

data _+_+_ {a b c} (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where 
  inl : A → A + B + C
  inm : B → A + B + C
  inr : C → A + B + C

data +4 {a b c d} (A : Set a) (B : Set b) (C : Set c) (D : Set d) 
                : Set (a ⊔ b ⊔ c ⊔ d) where 
  inll : A → +4 A B C D
  inlm : B → +4 A B C D
  inrm : C → +4 A B C D
  inrr : D → +4 A B C D

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ refl ]≡ y = x ≡ y
