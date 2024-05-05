{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Product using (proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_)
  renaming (trans to _∙_)

open import Simple

module SimpleUtils where

collect-snd : ∀ {F A} ⦃ _ : Functor F ⦄ (xs : F A)
            → fmap proj₂ (collect xs (all _ id xs)) ≡ xs
collect-snd xs = discard-coh (collect xs (all _ id xs)) ∙ fmap-id xs

Fix-fold : ∀ {F A} ⦃ _ : Functor F ⦄ → (F A → A) → Fix F → A
Fix-fold f xs 
  = Fix-elim _ (λ d ps → f (replace _ ps)) xs

unfix : ∀ {F} ⦃ _ : Functor F ⦄ → Fix F → F (Fix F)
unfix xs = Fix-fold (fmap fix) xs


open import Data.Product using (_,_; proj₁)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl)

crazy : Set → Set → Set → Set
crazy A B X = A → B → X

instance 
  crazy-functor : ∀ {A B} → Functor (crazy A B)
crazy-functor .All f g = ∀ x y → f (g x y)
crazy-functor .all P p xs x y = p (xs x y)
crazy-functor .collect xs ps x y = xs x y , ps x y
crazy-functor .discard f x y = proj₂ (f x y)
crazy-functor .discard-coh xs = refl
crazy-functor .collect-fst xs p = refl
crazy-functor .fmap-id xs = refl
crazy-functor .fmap-comp f g xs = refl


crazyD : Set → Set → Set
crazyD A B = Fix (crazy A B)

uhh : ∀ {A B} → Fix (crazy A B)
uhh {A} {B} = fix {F = crazy A B} (λ x y → {!!})

data CrazyIso (A B : Set) : Set where
  mk : (A → B → CrazyIso A B) → CrazyIso A B

-- wha : ∀ {A B} → crazyD A B → A
-- wha p = Fix-fold (λ ahh → {!!}) p  -- Fix-elim _ (λ d ps → ps {!!} {!!}) p


-- data Foo : Set where
--   MkFoo : A → B → Foo

