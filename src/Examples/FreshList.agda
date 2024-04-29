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
open import Data.Empty using (⊥)
open import Function using (case_of_)

open import IndRec
open import IndRecUtils
open import Examples.FreshList.Encoding renaming ([] to []#)

-- WIP port of https://agda.github.io/agda-stdlib/Data.List.Fresh.html
-- No universe polymorphism because I don't want to deal with universe levels...
module Examples.FreshList where

private
  variable
    A : Set
    B : Set

module _ (A : Set) (R : Rel A 0ℓ) where
  List# : Set
  List# = Fix (List#D A) ⦃ List#D-Functor _ R ⦄

  fresh : A → List# → Set
  fresh x xs = fixInterpret xs x

infixr 5 _∷#_
pattern _∷#_ x xs = cons x xs _

-- Convenient notation for freshness making A and R implicit parameters
infix 5 _#_
_#_ : ∀ {A R} (a : A) (as : List# A R) → Set
_#_ = fresh _ _

------------------------------------------------------------------------
-- Operations for modifying fresh lists

module _ {A B} {R : Rel A 0ℓ} {S : Rel B 0ℓ} 
         (f : A → B) (R⇒S : ∀[ R ⇒ (S on f) ]) where

  map-simul : ∀ (as : List# A R) → Σ (List# B S) 
                                     (λ bs → ∀ {a} → a # as → f a # bs)
  map-simul = Fix-elim _ 
    (λ where []# tt → fix []# , (λ where tt → tt) 
             (cons a as fr) (map , map-#) → fix (cons (f a) map (map-# fr)) 
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

------------------------------------------------------------------------
-- Views (now predicates because green slime is scary!)

Empty : ∀ {A R} → List# A R → Set
Empty xs = case unfix xs of λ where
  []#      → ⊤
  (_ ∷# _) → ⊥

NonEmpty : ∀ {A R} → List# A R → Set
NonEmpty xs = case unfix xs of λ where
  []#      → ⊥
  (_ ∷# _) → ⊤

------------------------------------------------------------------------
-- Operations for reducing fresh lists

length : ∀ {R} → List# A R → ℕ
length = Fix-fold (λ where []# → 0; (_ ∷# xs) → suc xs)

------------------------------------------------------------------------
-- Operations for constructing fresh lists

[_]# : ∀ {R} → A → List# A R
[ a ]# = fix (a ∷# fix []#)

fromMaybe : ∀ {R} → Maybe A → List# A R
fromMaybe nothing  = fix []#
fromMaybe (just a) = [ a ]#

module _ {R : Rel A 0ℓ} (R-refl : B.Reflexive R) where

  replicate   : ℕ → A → List# A R
  replicate-# : (n : ℕ) (a : A) → a # replicate n a

  replicate zero    a = fix []#
  replicate (suc n) a = fix (cons a (replicate n a) (replicate-# n a))

  replicate-# zero    a = _
  replicate-# (suc n) a = R-refl , replicate-# n a

------------------------------------------------------------------------
-- Operations for deconstructing fresh lists

uncons : ∀ {R} → List# A R → Maybe (A × List# A R)
uncons xs = case unfix xs of λ where
  []#       → nothing
  (a ∷# as) → just (a , as)

head : ∀ {R} → List# A R → Maybe A
head = Maybe.map proj₁ ∘′ uncons

tail : ∀ {R} → List# A R → Maybe (List# A R)
tail = Maybe.map proj₂ ∘′ uncons

take-simul : ∀ {R} (n : ℕ) (as : List# A R) 
           → Σ (List# A R) (λ as′ → ∀ a → a # as → a # as′)
take-simul zero = Fix-elim _ λ _ _ → fix []# , λ a → _
take-simul (suc n) = Fix-elim _ λ where
  []# p → fix []# , _
  (cons x xs fr) (take , take-#) → fix (cons x take (take-# x fr)) 
                                 , λ a (p , ps) → p , take-# a ps

take   : ∀ {R} → ℕ → List# A R → List# A R
take n = proj₁ ∘ take-simul n

take-# : ∀ {R} n a (as : List# A R) → a # as → a # take n as
take-# n a as = proj₂ (take-simul n as) a

drop : ∀ {R} → ℕ → List# A R → List# A R
drop zero    as = as
drop (suc n) as = case unfix as of λ where
  []# → fix []#
  (a ∷# as) → drop n as
