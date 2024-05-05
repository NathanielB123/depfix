{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Product using (∃; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)

open import Indexed

module IndexedUtils where

Fix-fold : ∀ {M F A} ⦃ _ : Functor M F ⦄ 
         → (∀ {i} → F A i → A i) → ∀ {i} → Fix F i → A i
Fix-fold f = Fix-elim _ (λ d ps → f (replace d ps))

unfix≡ : ∀ {M F i} ⦃ _ : Functor M F ⦄ → (xs : Fix F i) → ∃ (λ ys → fix ys ≡ xs)
unfix≡ xs 
  = Fix-elim (λ _ xs′ → ∃ (λ ys → fix ys ≡ xs′)) (λ xs′ ps → xs′ , refl) xs

unfix : ∀ {M F i} ⦃ _ : Functor M F ⦄ → Fix F i → F (Fix F) i
unfix = proj₁ ∘ unfix≡
