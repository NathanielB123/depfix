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
    List#D-Functor .All = List#D-All
    List#D-Functor .all = List#D-all
    List#D-Functor .collect = List#D-collect
    List#D-Functor .identity [] = refl
    List#D-Functor .identity (cons x xs a) = refl
    List#D-Functor .composition f g [] = refl
    List#D-Functor .composition f g (cons x xs a) = refl
    List#D-Functor .interpret = freshD

instance
  List#D-Functor-inst : ∀ {A R} → Functor (A → Set) (List#D A)
List#D-Functor-inst {R = R} = List#D-Functor _ R


List#DFoldable : ∀ {A} R → Foldable (A → Set) (List#D A)
List#DFoldable R .functor = List#D-Functor _ R
List#DFoldable _ .fold-interpret [] _ = ⊥
List#DFoldable _ .fold-interpret (cons x xs _) _ = fixInterpret xs x
List#DFoldable _ .collect-fix [] tt = inl tt
List#DFoldable _ .collect-fix (cons x xs f) p = cons x p f

instance
  List#DFoldable-inst : ∀ {A R} → Foldable (A → Set) (List#D A)
List#DFoldable-inst {R = R} = List#DFoldable R 
