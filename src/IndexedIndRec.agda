{-# OPTIONS --cubical-compatible --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module IndexedIndRec where

-- We break 'fixInterpret' off from the main definition of 'Functor' here to 
-- allow for a bit of extra flexibility when implementing such functions
--
-- Perhaps an alternative design could involve having special behaviour for if
-- M is itself a 'Functor' (i.e. having 'interpret' no longer return just 'M')
record PreFunctor (I : Set) (M : Set₁) 
                  (F : (A : I → Set) → (∀ i → A i → M) → I → Set) : Set₁ where
  field
    All : ∀ {A ι} (P : ∀ i → A i → Set) {i} → F A ι i → Set
    all : ∀ {A ι} (P : ∀ i → A i → Set) (p : ∀ {i} x → P i x) {i} (xs : F A ι i)
        → All P xs
    
    collect : ∀ {A P ι i} (xs : F A ι i) → All P xs 
            → F (λ i → Σ (A i) (P i)) (λ i → ι i ∘ proj₁) i 
    discard : ∀ {A B : I → Set} {ι i} 
            → F (λ i → A i × B i) (λ i → ι i ∘ proj₂) i → F B ι i

  fmap : ∀ {A B i} {ι : I → M} → (∀ {i} → A i → B i) 
       → F A (λ i _ → ι i) i → F B (λ i _ → ι i) i
  fmap f xs = discard (collect xs (all _ f xs))

  field
    discard-coh : ∀ {A B : I → Set} {ι : I → M} {i} 
                    (xs : F (λ i → A i × B i) (λ i _ → ι i) i)
                → fmap proj₂ xs ≡ discard xs
    collect-fst : ∀ {A P} {ι : I → M} (p : ∀ {i} x → P i x)
                    {i} (xs : F A (λ i _ → ι i) i) 
                → fmap proj₁ (collect xs (all P p xs)) ≡ xs
    fmap-id     : ∀ {A} {ι : I → M} {i} (xs : F A (λ i _ → ι i) i) 
                → fmap id xs ≡ xs
    fmap-comp   : ∀ {A B C : I → Set} {ι : I → M}
                    (f : ∀ {i} → A i → B i) (g : ∀ {i} → B i → C i) 
                    {i} (xs : F A (λ i _ → ι i) i) 
                → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs

open PreFunctor ⦃...⦄ public

postulate
  Fix : ∀ {I M} F → ⦃ PreFunctor I M F ⦄ → I → Set

record Functor (I : Set) (M : Set₁) 
               (F : (A : I → Set) → (∀ i → A i → M) → I → Set) : Set₁ where
  field
    ⦃ prefunc ⦄ : PreFunctor I M F
    fixInterpret : ∀ i → Fix F i → M

open Functor ⦃...⦄ public

postulate
  fix : ∀ {I M F i} ⦃ _ : Functor I M F ⦄ → F (Fix F) fixInterpret i → Fix F i
  Fix-elim : ∀ {I M F} ⦃ _ : Functor I M F ⦄ P
           → (∀ {i} (d : F (Fix F) _ i) → All P d → P i (fix d))
           → ∀ {i} xs → P i xs
  fixβ     : ∀ {I M F} ⦃ _ : Functor I M F ⦄ P 
               (m : ∀ {i} (d : F (Fix F) _ i) → All P d → P i (fix d)) 
               {i} (d : F (Fix F) _ i)
           → Fix-elim P m (fix d) ≡ m d (all P (Fix-elim P m) d)

unfix : ∀ {I M F} ⦃ _ : Functor I M F ⦄ {i} → Fix F i → F (Fix F) fixInterpret i
unfix = Fix-elim _ (λ xs ps → xs)

-- Functor with 'fixInterpret' defined recursively instead of in one go
record RecFunctor (I : Set) (M₁ : Set₁) (M₂ : Set₁) 
                (F : (A : I → Set) → (∀ i → A i → M₂) → I → Set) : Set₁ where
  field
    interpret : ∀ {A i} ι → F A ι i → M₁
open RecFunctor ⦃...⦄ public

postulate
  fixInterpretRec : ∀ {I M₁ M₂ F} ⦃ _ : RecFunctor I M₁ M₂ F ⦄ ⦃ _ : PreFunctor I M₂ F ⦄ i → Fix F i → M₁
  fixInterpretRecβ : ∀ {I M₁ M₂ F}  ⦃ _ : RecFunctor I M₁ M₂ F ⦄ ⦃ f : Functor I M₂ F ⦄ i 
                       (xs : F (Fix F) fixInterpret i)
                   → fixInterpretRec i (fix xs)
                   ≡ interpret fixInterpret xs 

{-# REWRITE fixβ fixInterpretRecβ #-}
