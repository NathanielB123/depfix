{-# OPTIONS --cubical-compatible --rewriting --local-confluence-check #-}

open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong)
  renaming (trans to _∙_)

open import Simple

module SimpleUtils where

-- A utility for "collecting" together elements and proofs that P holds for them
-- into the 'Functor' rather than just "replacing" the elements with new ones
-- produced by a non-dependent 'p'

-- Peio Borthelle on the Agda Zulip originally came up with this 'collect' op/
-- 'collect-fst' law as a way to perhaps strengthen my non-dependent 'Functor' 
-- laws, but it turns out that doing so is superfluous - the existing 'Functor' 
-- laws are powerful enough to prove 'collect-fst' using this impl!
-- https://agda.zulipchat.com/#narrow/stream/238741-general/topic/Formalising.20Inductive.20Types/near/433118420

-- This isn't the end of the story though! It turns out, when extending this
-- construction to handle induction-recursion, 'collect' becomes useful again!
module _ {F} ⦃ _ : Functor F ⦄ where
  AllP : ∀ {A} (P : A → Set) → F A → Set
  AllP P = All (λ _ → ∃ P)

  allP : ∀ {A} (P : A → Set) (p : ∀ x → P x) xs → AllP P xs
  allP P p = all _ (λ x → x , p x)

  -- With this impl, 'collect' for 'AllP' is literally the same operation as 
  -- 'replace' for 'All'
  collect :  ∀ {A P} (xs : F A) (ps : AllP P xs) → F (Σ A P)
  collect = replace

  collect-fst : ∀ {A P} (xs : F A) p 
                → fmap proj₁ (collect xs (allP P p xs)) ≡ xs
  collect-fst xs p = fmap-comp (λ x → x , p x) proj₁ xs ∙ fmap-id xs
  
  collect-snd : ∀ {A} (xs : F A) → fmap proj₂ (collect _ (allP _ id xs)) ≡ xs
  collect-snd xs = fmap-comp (λ x → x , x) proj₂ xs ∙ fmap-id xs

  Fix-fold : ∀ {A} → (F A → A) → Fix F → A
  Fix-fold f xs 
    = Fix-elim _ (λ d ps → f (replace _ ps)) xs

  unfix : Fix F → F (Fix F)
  unfix = Fix-elim _ (λ xs _ → xs)

  -- We cannot turn this into a definitional rewrite without losing confluence 
  -- due to how Fix-elim must block on expecting "fix d"
  -- e.g. consider 
  -- > Fix-elim _ _ (fix (unfix xs))
  -- - If we don't cancel the adjacent fix-unfix, then we are able to apply 
  --   fixβ.
  -- - If we do cancel the adjacent fix-unfix, then we are left with a stuck 
  --   term headed by Fix-elim.
  fix-unfix-id : ∀ xs → fix (unfix xs) ≡ xs
  fix-unfix-id = Fix-elim (λ xs → fix (unfix xs) ≡ xs) 
                          (λ xs _ → refl)
