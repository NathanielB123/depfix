{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Product using (_×_; Σ; _,_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (id; _∘_)
open import Data.Empty using (⊥)

open import IndRec
open import IndRecUtils
open import Utils

module Examples.FreshList.Encoding where

module _ (A : Set) where

  List#D : (L : Set) → (L → A → Set) → Set
  List#D L fresh = ⊤ + Σ (A × L) (λ where (a , as) → fresh as a)

  pattern [] = inl tt
  pattern cons x xs f = inr ((x , xs) , f)

  List#D-All : ∀ {L i} (P : L → Set) → List#D L i → Set
  List#D-All P [] = ⊤
  List#D-All P (cons _ xs _) = P xs

  List#D-all : ∀ {L i} (P : L → Set) (p : ∀ x → P x) (xs : List#D L i) 
            → List#D-All P xs
  List#D-all P p [] = tt
  List#D-all P p (cons x xs a) = p xs

  List#D-collect : ∀ {A B C} (xs : List#D A (λ _ → C)) 
                  → List#D-All (λ _ → B) xs → List#D B (λ _ → C)
  List#D-collect [] tt = []
  List#D-collect (cons x xs a) p = cons x p a

  module _ (R : Rel A 0ℓ) where

    freshD : ∀ {L} r → List#D L r → A → Set
    freshD r [] a = ⊤
    freshD r (cons x xs _) a = R a x × r xs a

    List#D-Functor : Functor (A → Set) List#D
    List#D-Functor .interpret = freshD
    List#D-Functor .All P [] = ⊤
    List#D-Functor .All P (cons _ xs _) = P xs
    List#D-Functor .all P p [] = tt
    List#D-Functor .all P p (cons x xs a) = p xs
    List#D-Functor .collect [] tt = []
    List#D-Functor .collect (cons x xs a) p = cons x (xs , p) a
    List#D-Functor .discard [] = []
    List#D-Functor .discard (cons x (xs , p) a) = cons x p a
    List#D-Functor .discard-coh [] = refl
    List#D-Functor .discard-coh (cons _ _ _) = refl
    List#D-Functor .collect-pairs [] _ = refl
    List#D-Functor .collect-pairs (cons _ _ _) _ = refl
    List#D-Functor .fmap-id [] = refl
    List#D-Functor .fmap-id (cons _ _ _) = refl
    List#D-Functor .fmap-comp f g [] = refl
    List#D-Functor .fmap-comp f g (cons _ _ _) = refl

instance
  List#D-Functor-inst : ∀ {A R} → Functor (A → Set) (List#D A)
List#D-Functor-inst {R = R} = List#D-Functor _ R
