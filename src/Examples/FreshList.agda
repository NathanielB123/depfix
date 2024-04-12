{-# OPTIONS --cubical-compatible --rewriting #-}

open import Level using (Level; _⊔_; 0ℓ)
open import Data.Bool.Base using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product.Base using (∃; _×_; _,_; -,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∘′_; flip; id; _on_)
open import Relation.Nullary using (does)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (Σ)
import Relation.Binary.Definitions as B
open import Relation.Nary
open import Function.Base using (_∘_)

open import IndRec
open import Examples.FreshList.Encoding renaming ([] to []#)

-- WIP port of https://agda.github.io/agda-stdlib/Data.List.Fresh.html
module Examples.FreshList where

private
  variable
    A : Set
    B : Set

module _ (A : Set) (R : Rel A 0ℓ) where
  List# : Set
  List# = Fix (List#D A R) ⦃ List#D-Functor2 {R = R} ⦄

  fresh : A → List# → Set
  fresh x xs = fixInterpret xs x

infixr 5 _∷#_
pattern _∷#_ x xs = cons x xs _

-- Convenient notation for freshness making A and R implicit parameters
infix 5 _#_
_#_ : ∀ {A} {R : Rel A 0ℓ} (a : A) (as : List# A R) → Set
_#_ = fresh _ _

------------------------------------------------------------------------
-- Operations for modifying fresh lists

module _ {A B} {R : Rel A 0ℓ} {S : Rel B 0ℓ} 
         (f : A → B) (R⇒S : ∀[ R ⇒ (S on f) ]) where

  map-simul : ∀ (as : List# A R) → Σ (List# B S) 
                                     (λ bs → ∀ {a} → a # as → f a # bs)
  map-simul 
    = Fix-elim _ (λ where []# tt → fix []# , (λ where tt → tt) 
                          (cons a as fr) (bs , map-#) 
                            → fix (cons (f a) bs (map-# fr)) 
                            , λ where (p , ps) → R⇒S p , map-# ps)

  map : List# A R → List# B S
  map = proj₁ ∘ map-simul

  map-# : ∀ {a} as → a # as → f a # map as
  map-# xs = proj₂ (map-simul xs)

module _ {R : Rel B 0ℓ} (f : A → B) where

  map₁ : List# A (R on f) → List# B R
  map₁ = map f id

module _ {R : Rel A 0ℓ} {S : Rel A 0ℓ} (R⇒S : ∀[ R ⇒ S ]) where

  map₂ : List# A R → List# A S
  map₂ = map id R⇒S
