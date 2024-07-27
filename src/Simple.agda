{-# OPTIONS --cubical-compatible --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_) 
open import Function.Base using (id; _∘_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Level using (Level; Setω)

open import Utils

module Simple where

-- We let 'All'/'all' work with predicates of any universe level to support
-- large elimination. Note we could also parameterise over the level of 'F' but
-- all the examples work fine with Set₀, so I have stuck with that for cleaner
-- demonstration and better type inference.
variable
  Pℓ : Level

record Functor (F : Set → Set) : Setω where
  field
    -- 'All' lifts a given predicate over the functor
    -- Naming of 'All'/'all'/'replace' originates from 
    -- https://personal.cis.strath.ac.uk/conor.mcbride/levitation.pdf
    All     : ∀ {A} (P : A → Set Pℓ) → F A → Set Pℓ
    all     : ∀ {A} (P : A → Set Pℓ) (p : ∀ x → P x) xs → All P xs
    replace : ∀ {A B} (xs : F A) (ps : All (λ _ → B) xs) → F B
  
  fmap : ∀ {A B} → (A → B) → F A → F B
  fmap f xs = replace xs (all _ f xs)

  field
    fmap-comp   : ∀ {A B C} (f : A → B) (g : B → C) xs 
                → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs
    fmap-id     : ∀ {A} (xs : F A) → fmap id xs ≡ xs

open Functor ⦃...⦄ public

postulate
  Fix : ∀ (F : Set → Set) → ⦃ Functor F ⦄ → Set
  fix : ∀ {F : Set → Set} ⦃ _ : Functor F ⦄ → F (Fix F) → Fix F
  Fix-elim : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set Pℓ) 
           → ((d : F (Fix F)) → All P d → P (fix d)) → ∀ x → P x
  -- We might hope for a Fix-elim which doesn't block on expecting a "fix d"
  -- i.e. something like
  -- > Fix-elim P m d ≡ m (unfix d) (all P (Fix-elim P m) (unfix d))
  -- Unfortunately, in practice, this causes typechecker loops
  fixβ : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set Pℓ) 
           (m : (d : F (Fix F)) → All P d → P (fix d)) d 
       → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

{-# REWRITE fixβ #-}

-- Alternatively, we can implement these postulates with an Agda datatype. 

-- Agda of course won't accept that 'Fix' is strictly positive (for
-- one, our scheme allows encoding non-strictly positive functors so this
-- is kind of inevitable, but even if Agda allowed non-strictly positive
-- inductive definitions, 'Fix' still doesn't satisfy this criteria
-- syntactically/definitionally)

-- Agda also won't accept Fix-elim, as defined below, as terminating.
-- Termination here hinges on 'all' only calling 'Fix-elim P p' on smaller terms
-- than 'fix x'. This is enforced by the definition of 'Functor': type 'A' is
-- abstract, so (assuming parametricity) the only way to get one's hands on a 
-- value of that type is via breaking apart the 'xs'. Perhaps we could convince
-- Agda of termination here by adding an additional law or two to 'Functor' and
-- using well-founded induction, but I don't think the extra noise would be 
-- worth it.

-- {-# NO_POSITIVITY_CHECK #-}
-- data Fix (F : Set → Set) ⦃ f : Functor F ⦄ : Set where
--   fix : F (Fix F) → Fix F

-- {-# TERMINATING #-}
-- Fix-elim : ∀ {F} ⦃ _ : Functor F ⦄ (P : Fix F → Set Pℓ) 
--          → ((d : F (Fix F)) → All P d → P (fix d)) → ∀ x → P x
-- Fix-elim P p (fix x) = p x (all P (Fix-elim P p) x)
