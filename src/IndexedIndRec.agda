{-# OPTIONS --cubical-compatible --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module IndexedIndRec where

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

-- Functor with 'fixInterpret' defined incrementally
record IncFunctor (I : Set) (M : Set₁) 
                (F : (A : I → Set) → (∀ i → A i → M) → I → Set) : Set₁ where
  field
    ⦃ prefunc ⦄ : PreFunctor I M F
    interpret : ∀ {A i} ι → F A ι i → M
open IncFunctor ⦃...⦄ public

postulate
  fixInterpretInc : ∀ {I M F} ⦃ _ : IncFunctor I M F ⦄ i → Fix F i → M
  fixInc : ∀ {I M F i} ⦃ _ : IncFunctor I M F ⦄ → F (Fix F) fixInterpretInc i 
         → Fix F i

IncFunctor→Functor : ∀ {I M F} → ⦃ IncFunctor I M F ⦄ → Functor I M F
IncFunctor→Functor .fixInterpret = fixInterpretInc

unfix : ∀ {I M F} ⦃ _ : Functor I M F ⦄ {i} → Fix F i → F (Fix F) fixInterpret i
unfix {F = F} = Fix-elim (λ i _ → F (Fix F) fixInterpret i) (λ xs ps → xs)

postulate 
  fixIncConf : (λ {I M F i} ⦃ _ : IncFunctor I M F ⦄ → fixInc {I} {M} {F} {i}) 
             ≡ fix ⦃ IncFunctor→Functor ⦄

  fixInterpretIncβ : ∀ {I M F}  ⦃ _ : IncFunctor I M F ⦄ i 
                       (xs : Fix F i)
                   → fixInterpretInc i xs
                   ≡ interpret fixInterpretInc (unfix ⦃ IncFunctor→Functor ⦄ xs)  
  -- unfix (fix xs) ≡ xs holds by definition, but I don't think 
  -- fix (unfix xs) ≡ xs is provable...
  fix-unfix-id : ∀ {I M F i} ⦃ _ : Functor I M F ⦄ (xs : Fix F i) 
               → fix (unfix xs) ≡ xs

{-# REWRITE fixβ fixInterpretIncβ fixIncConf fix-unfix-id #-}

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Bool using (Bool; true; false)
open import Level using (lift; lower; Lift; 0ℓ; suc)
open import Function using (case_of_)

open import Utils

module TTinTT where


  data CtxD (CtxR : Set) (TyR : CtxR → Set) : Set where
    ε   : CtxD CtxR TyR
    _,_ : ∀ Γ → TyR Γ → CtxD CtxR TyR

  TyPre : ∀ {CtxR TyR} → CtxD CtxR TyR → Set

  instance 
    CtxD-PreFunctor : PreFunctor ⊤ Set (λ where C r tt → CtxD (C tt) (r tt))
  CtxD-PreFunctor .All P ε = ⊤
  CtxD-PreFunctor .All P (Γ , A) = P tt Γ
  CtxD-PreFunctor .all P p ε = tt
  CtxD-PreFunctor .all P p (Γ , A) = p Γ
  CtxD-PreFunctor .collect ε tt = ε
  CtxD-PreFunctor .collect (Γ , A) PΓ = (Γ , PΓ) , A
  CtxD-PreFunctor .discard ε = ε
  CtxD-PreFunctor .discard ((Γ , PΓ) , A) = PΓ , A
 
  CtxD-PreFunctor .discard-coh ε = refl
  CtxD-PreFunctor .discard-coh (Γ , A) = refl
  CtxD-PreFunctor .collect-fst _ ε = refl
  CtxD-PreFunctor .collect-fst _ (Γ , A) = refl
  CtxD-PreFunctor .fmap-id ε = refl
  CtxD-PreFunctor .fmap-id (Γ , A) = refl
  CtxD-PreFunctor .fmap-comp _ _ ε = refl
  CtxD-PreFunctor .fmap-comp _ _ (Γ , A) = refl

  instance
    CtxD-IncFunctor : IncFunctor ⊤ Set (λ where C r tt → CtxD (C tt) (r tt))
    CtxD-IncFunctor .interpret ι Γ = TyPre Γ

  instance CtxD-Functor : Functor ⊤ Set (λ where C r tt → CtxD (C tt) (r tt))
  CtxD-Functor = IncFunctor→Functor

  Ctx : Set
  Ctx = Fix (λ where C r tt → CtxD (C tt) (r tt)) tt

  data TyPreD {CtxR TyR} (TyPreR : CtxD CtxR TyR → Set)
              (,R : (Γ : CtxD CtxR TyR) → TyPreR Γ → Lift (suc 0ℓ) (CtxD CtxR TyR))
              (Γ : CtxD CtxR TyR) : Set 
              where
    U : TyPreD TyPreR ,R Γ
    Π : (A : TyPreR Γ) → TyPreR (lower (,R Γ A))
      → TyPreD TyPreR ,R Γ

  -- TODO: Fill at the rest of the functor stuff for types
  instance 
    TyPreD-PreFunctor : ∀ {CtxR TyR} 
                      → PreFunctor (CtxD CtxR TyR) _ TyPreD
  
  TyPre = Fix TyPreD

  instance
    TyPreD-Functor : Functor (CtxD Ctx (fixInterpret tt)) _ TyPreD
  TyPreD-Functor .prefunc = TyPreD-PreFunctor
  TyPreD-Functor .fixInterpret Γ A = lift (fix Γ , A)

  Ty : Ctx → Set
  Ty Γ = TyPre (unfix Γ)

  _,c_ : ∀ Γ → Ty Γ → Ctx
  Γ ,c A = fix (Γ , A)

  Πtest : ∀ {Γ} (A : Ty Γ) → Ty (Γ ,c A) → Ty Γ
  Πtest A B = fix (Π A B)


     