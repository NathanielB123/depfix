{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst)
  renaming (trans to _∙_)
open import Level using (Level; Lift; lift; 0ℓ; _⊔_)

open import Utils
open import Simple
open import SimpleUtils

module Examples.Forest where

-- Aim: Derive the induction principle for Forests outlined in
-- https://libres.uncg.edu/ir/asu/f/Johann_Patricia_2020_Deep%20Induction_fossacs.pdf
-- Key Observation: Their "List^ Q xs" looks a lot like our 
-- 'All {F = List} Q xs'

ListD : Set → Set → Set
ListD A ListR = ⊤ + (A × ListR)

pattern nil = inl tt
pattern cons x xs = inr (x , xs)

instance
  ListD-Functor : ∀ {A} → Functor (ListD A)
  ListD-Functor .All P nil = Lift _ ⊤
  ListD-Functor .All P (cons x xs) = P xs
  ListD-Functor .all P p nil = lift tt
  ListD-Functor .all P p (cons x xs) = p xs
  ListD-Functor .replace nil (lift tt) = nil
  ListD-Functor .replace (cons x xs) ys = cons x ys

  ListD-Functor .fmap-comp f g nil = refl
  ListD-Functor .fmap-comp f g (cons _ _) = refl
  ListD-Functor .fmap-id nil = refl
  ListD-Functor .fmap-id (cons _ _) = refl

List : Set → Set
List A = Fix (ListD A)

List-All : ∀ {A} (P : A → Set Pℓ) → List A → Set Pℓ 
List-All P 
  = Fix-elim (λ _ → Set _) (λ where nil (lift tt) → Lift _ ⊤
                                    (cons x xs) Pxs → P x × Pxs) 

List-all : ∀ {A} (P : A → Set Pℓ) (p : ∀ x → P x) (xs : List A) → List-All P xs
List-all P p
  = Fix-elim _ (λ where nil (lift tt) → lift tt
                        (cons x xs) Pxs → p x , Pxs) 

List-replace : ∀ {A B} (xs : List A) (ps : List-All (λ _ → B) xs) → List B
List-replace 
  = Fix-elim (λ xs → List-All _ xs → _)
               (λ where nil (lift tt) (lift tt) → fix nil
                        (cons x xs) r (y , ys) → fix (cons y (r ys)))

List-fmap : ∀ {A B} → (A → B) → List A → List B
List-fmap f xs = List-replace xs (List-all _ f xs)

List-fmap-comp : ∀ {A B C} (f : A → B) (g : B → C) (xs : List A) 
                → List-fmap g (List-fmap f xs) ≡ List-fmap (g ∘ f) xs
List-fmap-comp f g = Fix-elim _  (λ where nil (lift tt) → refl
                                          (cons x xs) → cong (fix ∘ cons _))

List-fmap-id : ∀ {A} (xs : List A) → List-fmap id xs ≡ xs
List-fmap-id = Fix-elim _ (λ where nil (lift tt) → refl
                                   (cons x xs) → cong (fix ∘ cons _))

instance
  List-Functor : Functor List
  List-Functor .All = List-All 
  List-Functor .all = List-all
  List-Functor .replace = List-replace
  List-Functor .fmap-comp = List-fmap-comp
  List-Functor .fmap-id = List-fmap-id


ForestD : Set → Set → Set
ForestD A ForestR = ⊤ + (A × List ForestR)

instance
  ForestD-Functor : ∀ {A} → Functor (ForestD A)
  ForestD-Functor .All P nil = Lift _ ⊤
  ForestD-Functor .All P (cons x xs) = All P xs
  ForestD-Functor .all P p nil = lift tt
  ForestD-Functor .all P p (cons x xs) = all P p xs
  ForestD-Functor .replace nil (lift tt) = nil
  ForestD-Functor .replace (cons x xs) ys = cons x (replace xs ys)

  ForestD-Functor .fmap-comp f g nil = refl
  ForestD-Functor .fmap-comp f g (cons _ xs) = cong (cons _) (fmap-comp _ _ xs)
  ForestD-Functor .fmap-id nil = refl
  ForestD-Functor .fmap-id (cons _ xs) = cong (cons _) (fmap-id xs)

Forest : Set → Set
Forest A = Fix (ForestD A)

-- TODO: I arrived at most of the below utilities via symbol-pushing until it
-- typechecked. It might be possible to significantly simplify.
-- At the very least, we should probably move these utilities into SimpleUtils
merge : ∀ {A} (xs : List A) → All (λ _ → Set Pℓ) xs → Set Pℓ
merge = Fix-elim (λ xs → All _ xs → _) 
                 (λ where nil (lift tt) (lift tt)  → Lift _ ⊤
                          (cons x xs) r (Px , Pxs) → Px × r Pxs)

Forest-All : ∀ {A} (P : A → Set Pℓ) → Forest A → Set Pℓ 
Forest-All P
  = Fix-elim (λ _ → Set _) (λ where nil (lift tt) → Lift _ ⊤
                                    (cons x xs) Pxs → P x × merge xs Pxs)

All-inner : ∀ {A} (P : A → Set Pℓ) → List (Forest A) → Set Pℓ
All-inner P xs 
  = merge xs (all _ (λ xs → Forest-All P xs) xs)

All-app : ∀ {A} (P : Forest A → Set Pℓ) (Q : A → Set Pℓ) 
            (xs : List (Forest A))   
        → All (λ x → Forest-All Q x → P x) xs → All-inner Q xs 
        → All P xs
All-app P Q
  = Fix-elim (λ xs → All _ xs → All-inner Q xs → All _ xs) 
             (λ where nil _ _ _ → lift tt
                      (cons x xs) r (Px , Pxs) (Qx , Qxs) → Px Qx , r Pxs Qxs) 

-- The "deep" induction principle for Forests!
Forest-elim : ∀ {A} (P : Forest A → Set Pℓ) (Q : A → Set Pℓ) → P (fix nil)
            → (∀ {x} ts → Q x → List-All P ts → P (fix (cons x ts)))
            → ∀ (x : Forest A) → Forest-All Q x → P x
Forest-elim P Q Pnil Pcons
  = Fix-elim (λ xs → Forest-All Q xs → P xs) 
             (λ where nil (lift tt) _ → Pnil
                      (cons x xs) Pxs (Qx , Qxs)
                        → Pcons xs Qx (All-app P Q xs Pxs Qxs))

-- 'Forest-elim' was the main goal of this example, but for fun, let's try and
-- also prove that 'Forest' is a 'Functor'

collect-merge : ∀ {A P} (xs : List (Forest A)) (ps : All (Forest-All P) xs) 
              → merge xs (all (λ _ → Set Pℓ) (Forest-All P) xs)
collect-merge = Fix-elim _ (λ where nil (lift tt) (lift tt) → lift tt
                                    (cons _ _) r (p , ps) → p , r ps)

Forest-all : ∀ {A} (P : A → Set Pℓ) (p : ∀ x → P x) (xs : Forest A) 
           → Forest-All P xs
Forest-all P p
    = Fix-elim _ (λ where nil (lift tt) → lift tt
                          (cons x xs) Pxs → p x , collect-merge xs Pxs)

Forest-replace : ∀ {A B} (xs : Forest A) (ps : Forest-All (λ _ → B) xs) → Forest B
Forest-replace
  = Forest-elim _ _ (fix nil) (λ ts x xs → fix (cons x (replace ts xs)))

Forest-fmap : ∀ {A B} → (A → B) → Forest A → Forest B
Forest-fmap f xs = Forest-replace xs (Forest-all _ f xs)

-- Implementing the 'all'/'replace' operations isn't too bad but the proofs are 
-- a nightmare! I'm pretty sure this is do-able, but finding the right induction
-- principle/lemmas to abstract out will be a significant challenge...

lemma : ∀ {A} (xs : List (Forest A))
    → let aa = (λ { nil (lift tt) _ → fix nil
              ; (cons x xs) Pxs (Qx , Qxs)
                  → fix
                    (cons Qx
                    (List-replace xs (All-app (λ _ → Forest A) (λ _ → A) xs Pxs Qxs)))
              }) in
  (List-replace xs
        (All-app (λ _ → Forest A) (λ _ → A) xs
        (List-all (λ z → Forest-All (λ _ → A) z → Forest A)
          (Fix-elim (λ z → Forest-All (λ _ → A) z → Forest A)
          aa) xs)
        (collect-merge xs (all (Forest-All (λ _ → A)) (Fix-elim (Forest-All (λ _ → A)) 
              (λ where nil (lift tt) → lift tt
                       (cons x xs) Pxs → id x , collect-merge xs Pxs)) xs))))
    ≡ xs
                          
lemma = Fix-elim _ (λ where nil (lift tt) → refl
                            (cons x xs) eqs → cong fix (cong₂ cons {!!} {!!}))

Forest-fmap-id : ∀ {A} (xs : Forest A) → Forest-fmap id xs ≡ xs
Forest-fmap-id
  = Fix-elim _ (λ where nil (lift tt) → refl
                        (cons x xs) eq 
                          → let uhh = Fix-elim (λ xs → All _ xs → List-fmap id xs ≡ xs) 
                                                (λ where nil _ _ → {!!}
                                                         (cons _ _) _ _ → {!!}) xs eq
                             in cong (fix ∘ cons _) {!eq!})

Forest-fmap-comp : ∀ {A B C} (f : A → B) (g : B → C) xs 
                 → Forest-fmap g (Forest-fmap f xs) ≡ Forest-fmap (g ∘ f) xs
Forest-fmap-comp f g = {!!}

instance
  Forest-Functor : Functor Forest
  Forest-Functor .All = Forest-All 
  Forest-Functor .all = Forest-all
  Forest-Functor .replace = Forest-replace
 