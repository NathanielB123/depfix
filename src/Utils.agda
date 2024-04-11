{-# OPTIONS --cubical-compatible #-}

open import Level using (_⊔_)

module Utils where

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A + B
  inr : B → A + B

data _+_+_ {a b c} (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where 
  inl : A → A + B + C
  inm : B → A + B + C
  inr : C → A + B + C
