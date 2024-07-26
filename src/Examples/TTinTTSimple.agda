{-# OPTIONS --cubical-compatible --rewriting #-}

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; ∃; _×_) renaming (_,_ to _Σ,_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst; cong₂; sym)
open import Level using (Level; lift; lower; Lift; 0ℓ; suc)
open import Function using (id; _∘_; case_of_)
open import Data.Bool using (Bool; if_then_else_; true; false)

open import Utils
open import IndexedIndRec
open import IndexedIndRecUtils

-- A type-theory-in-type-theory-style inductive-inductive syntax
-- This example only includes contexts and types and is therefore much simpler
-- See Examples.TTinTT for ideas on how to deal with a third 
-- mutually inductive-inductive definition
module Examples.TTinTTSimple where

1ℓ : Level
1ℓ = suc 0ℓ

Ctx : Set
Ty : Ctx → Set

CtxD : (CtxR : Set) → (CtxR → Set) → Set
CtxD CtxR TyR = ⊤ + ∃ TyR

pattern ε = inl tt
pattern _,_ Γ A = inr (Γ Σ, A)

TyPreD : ∀ {CtxR TyR} (TyPreR : CtxD CtxR TyR → Set)
      → (∀ Γ → TyPreR Γ → Lift 1ℓ (CtxD CtxR TyR))
      → CtxD CtxR TyR → Set
TyPreD TyPreR ,R Γ = ⊤ + Σ (TyPreR Γ) (λ A → TyPreR (lower (,R Γ A)))

pattern U = inl tt
pattern Π A B = inr (A Σ, B)

TyPre : ∀ {CtxR TyR} → CtxD CtxR TyR → Set

instance 
  CtxD-PreFunctor : PreFunctor ⊤ _ (λ where C r tt → CtxD (C tt) (r tt))
  CtxD-PreFunctor .All P ε = ⊤
  CtxD-PreFunctor .All P (Γ , A) = P tt Γ
  CtxD-PreFunctor .all P p ε = tt
  CtxD-PreFunctor .all P p (Γ , A) = p Γ
  CtxD-PreFunctor .collect ε tt = ε
  CtxD-PreFunctor .collect (Γ , A) PΓ = (Γ Σ, PΓ) , A
  CtxD-PreFunctor .discard ε = ε
  CtxD-PreFunctor .discard ((Γ Σ, PΓ) , A) = PΓ , A

  CtxD-PreFunctor .discard-coh ε = refl
  CtxD-PreFunctor .discard-coh (Γ , A) = refl
  CtxD-PreFunctor .collect-pairs _ ε = refl
  CtxD-PreFunctor .collect-pairs _ (Γ , A) = refl
  CtxD-PreFunctor .fmap-id ε = refl
  CtxD-PreFunctor .fmap-id (Γ , A) = refl
  CtxD-PreFunctor .fmap-comp _ _ ε = refl
  CtxD-PreFunctor .fmap-comp _ _ (Γ , A) = refl

instance
  CtxD-RecFunctor : RecFunctor ⊤ _ _ (λ where C r tt → CtxD (C tt) (r tt))
  CtxD-RecFunctor .interpret ι Γ = TyPre Γ

instance CtxD-Functor : Functor ⊤ _ (λ where C r tt → CtxD (C tt) (r tt))
CtxD-Functor = RecFunctor→Functor

Ctx = Fix (λ where C r tt → CtxD (C tt) (r tt)) tt

instance 
  TyPreD-PreFunctor : ∀ {CtxR TyR} 
                    → PreFunctor (CtxD CtxR TyR) _ TyPreD
  TyPreD-PreFunctor .All P U = ⊤
  TyPreD-PreFunctor .All P (Π A B) = P _ A × P _ B
  TyPreD-PreFunctor .all P p U = tt
  TyPreD-PreFunctor .all P p (Π A B) = p A Σ, p B
  TyPreD-PreFunctor .collect U tt = U
  TyPreD-PreFunctor .collect (Π A B) (PA Σ, PB) = Π (A Σ, PA) (B Σ, PB)
  TyPreD-PreFunctor .discard U = U
  TyPreD-PreFunctor .discard (Π (A Σ, PA) (B Σ, PB)) = Π PA PB

  TyPreD-PreFunctor .discard-coh U = refl
  TyPreD-PreFunctor .discard-coh (Π _ _) = refl
  TyPreD-PreFunctor .collect-pairs _ U = refl
  TyPreD-PreFunctor .collect-pairs _ (Π _ _) = refl
  TyPreD-PreFunctor .fmap-id U = refl
  TyPreD-PreFunctor .fmap-id (Π _ _) = refl
  TyPreD-PreFunctor .fmap-comp _ _ U = refl
  TyPreD-PreFunctor .fmap-comp _ _ (Π _ _) = refl

TyPre = Fix TyPreD

instance
  TyPreD-Functor : Functor (CtxD Ctx (fixInterpret tt)) _ TyPreD
  TyPreD-Functor .prefunc = TyPreD-PreFunctor
  TyPreD-Functor .fixInterpret Γ A = lift (fix Γ , A)

Ty Γ = TyPre (unfix Γ)


-- Some very simple tests that the constructors actually work
,test : ∀ Γ → Ty Γ → Ctx
,test Γ A = fix (fix (unfix Γ) , A)

Πtest : ∀ {Γ} (A : Ty Γ) → Ty (,test Γ A) → Ty Γ
Πtest A B = fix (Π A B)