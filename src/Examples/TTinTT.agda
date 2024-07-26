{-# OPTIONS --cubical-compatible --rewriting --type-in-type #-}

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; ∃; _×_; proj₁; proj₂) renaming (_,_ to _Σ,_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst; cong; cong₂; sym)
open import Level using (Level; lift; lower; Lift; 0ℓ; suc)
open import Function using (id; _∘_; case_of_)
open import Data.Bool using (Bool; if_then_else_; true; false)

open import Utils
open import IndexedIndRec
open import IndexedIndRecUtils

-- A type-theory-in-type-theory-style inductive-inductive syntax (WIP)

-- I haven't added substitutions yet because doing this encoding by hand gets
-- extremely painful as the number of mutually inductive definitions increases
-- Hopefully, the pattern should be clear enough regardless

-- See Examples.TTinTTSimple for a (much) simpler example only including
-- contexts and types
module Examples.TTinTT where

1ℓ : Level
1ℓ = suc 0ℓ

Ctx : Set
Ty : Ctx → Set
Tm : ∀ Γ → Ty Γ → Set

CtxD : (CtxR : Set) → (CtxR → Set) → Set
CtxD CtxR TyR = ⊤ + ∃ TyR

pattern ε = inl tt
pattern _,_ Γ A = inr (Γ Σ, A)

-- We fuse the an isU predicate with a recursive call to Tm into TmUR to cut
-- down on the number of interpret functions we need to implement later. A
-- general algorithm which derived these datatypes and functor instances
-- automatically would probably not do this.
TyPreD : ∀ {CtxR TyR} (TyPreR : CtxD CtxR TyR → Set)
      → (∀ Γ → TyPreR Γ →  Lift 1ℓ (CtxD CtxR TyR) × Set)
      → CtxD CtxR TyR → Set
TyPreD TyPreR ,×TmUR Γ 
  = +4 ⊤ 
       (∃ λ A → TyPreR (,R Γ A))
       (∃ (TmUR Γ))
       (∃ λ Γ′ → Σ (TyPreR Γ′ × TyPreR Γ′) λ (A Σ, _) → Γ ≡ ,R Γ′ A)
  where ,R = λ Γ A → lower (proj₁ (,×TmUR Γ A))
        TmUR = λ Γ A → proj₂ (,×TmUR Γ A)

pattern U = inll tt
pattern Π A B = inlm (A Σ, B)
pattern El {A = A} M = inrm (A Σ, M)
pattern wk A B = inrr (_ Σ, (A Σ, B) Σ, refl)

TyPre : ∀ {CtxR TyR} → CtxD CtxR TyR → Set

-- We could also very easily add term weakening (vs).
-- Actually usable application relies on substitutions, which should be possible
-- but this encoding is already getting extremely painful

TmPreD : ∀ {CtxR TyR TyPreR ,×TmUR} 
           (,×Π×wkR : ∀ Γ (A : TyPreD TyPreR ,×TmUR Γ) 
                   →  Σ (CtxD CtxR TyR) (λ Γ,A
                   → (TyPreD TyPreR ,×TmUR Γ,A
                  → TyPreD TyPreR ,×TmUR Γ) 
                  × (TyPreD TyPreR ,×TmUR Γ
                  → TyPreD TyPreR ,×TmUR Γ,A)))
           (TmPreR : ∃ (TyPreD TyPreR ,×TmUR) → Set)
       → Σ (CtxD CtxR TyR) (TyPreD TyPreR ,×TmUR) → Set
TmPreD ,×Π×wkR TmPreR (Γ Σ, A)
  = (∃ λ A′ → ∃ λ B′ → TmPreR (_ Σ, B′) × A ≡ ΠR Γ A′ B′)
  + (∃ λ Γ′ → ∃ λ A′ → ∃ λ B′ → TmPreR (_ Σ, ΠR Γ′ A′ B′) 
     × Σ (Γ ≡ ,R Γ′ A′) λ Γ≡ → A ≡[ cong (TyPreD _ _) Γ≡ ]≡ B′)
  + (∃ λ Γ′ → ∃ λ A′ → Σ (Γ ≡ ,R Γ′ A′) λ Γ≡ 
     → A ≡[ cong (TyPreD _ _) Γ≡ ]≡ wkR Γ′ A′ A′)  
  where ,R = λ Γ A → proj₁ (,×Π×wkR Γ A)
        ΠR = λ Γ A → proj₁ (proj₂ (,×Π×wkR Γ A))
        wkR = λ Γ A → proj₂ (proj₂ (,×Π×wkR Γ A))

pattern lam M = inl (_ Σ, _ Σ, M Σ, refl)
pattern app M = inm (_ Σ, _ Σ, _ Σ, M Σ, refl Σ, refl)
pattern vz = inr (_ Σ, _ Σ, refl Σ, refl)

TmPre : ∀ {CtxR TyR TyPreR ,×TmUR} 
          (,×Π×wkR : ∀ Γ (A : TyPreD TyPreR ,×TmUR Γ) → Σ (CtxD CtxR TyR) (λ Γ,A 
                   → (TyPreD TyPreR ,×TmUR Γ,A → TyPreD TyPreR ,×TmUR Γ) 
                   × (TyPreD TyPreR ,×TmUR Γ → TyPreD TyPreR ,×TmUR Γ,A))) 
          (Γ : CtxD CtxR TyR) → TyPreD TyPreR ,×TmUR Γ 
      → Set

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
  TyPreD-PreFunctor .All P (El {A = A} M) = P _ A
  TyPreD-PreFunctor .All P (wk A B) = P _ A × P _ B
  -- TyPreD-PreFunctor .all P p U = tt
  -- TyPreD-PreFunctor .all P p (Π A B) = p A Σ, p B
  -- TyPreD-PreFunctor .collect U tt = U
  -- TyPreD-PreFunctor .collect (Π A B) (PA Σ, PB) = Π (A Σ, PA) (B Σ, PB)
  -- TyPreD-PreFunctor .discard U = U
  -- TyPreD-PreFunctor .discard (Π (A Σ, PA) (B Σ, PB)) = Π PA PB

  -- TyPreD-PreFunctor .discard-coh U = refl
  -- TyPreD-PreFunctor .discard-coh (Π _ _) = refl
  -- TyPreD-PreFunctor .collect-pairs _ U = refl
  -- TyPreD-PreFunctor .collect-pairs _ (Π _ _) = refl
  -- TyPreD-PreFunctor .fmap-id U = refl
  -- TyPreD-PreFunctor .fmap-id (Π _ _) = refl
  -- TyPreD-PreFunctor .fmap-comp _ _ U = refl
  -- TyPreD-PreFunctor .fmap-comp _ _ (Π _ _) = refl

TyPre = Fix TyPreD

instance
  TyPreD-RecFunctor : RecFunctor (CtxD Ctx (fixInterpret tt)) _ _ TyPreD
  TyPreD-RecFunctor .interpret {i = Γ} ,×TmUR U = TmPre {,×TmUR = ,×TmUR} {!!} Γ U
  TyPreD-RecFunctor .interpret ,×TmUR _ = ⊥

instance
  TyPreD-Functor : Functor (CtxD Ctx (fixInterpret tt)) _ TyPreD
  TyPreD-Functor .prefunc = TyPreD-PreFunctor
  TyPreD-Functor .fixInterpret Γ A .proj₁ = lift (fix Γ , A)
  TyPreD-Functor .fixInterpret Γ A .proj₂ = fixInterpretRec Γ A

instance
  TmPreD-PreFunctor : ∀ {CtxR TyR TyPreR ,×TmUR ,×Π×wkR} 
    → PreFunctor (Σ (CtxD CtxR TyR) (TyPreD TyPreR ,×TmUR)) 
                 (λ _ → ⊤) 
                 (λ TmPreR _ ΓA → TmPreD ,×Π×wkR TmPreR ΓA)

  TmPreD-Functor : ∀ {CtxR TyR TyPreR ,×TmUR ,×Π×wkR}
                 → Functor (Σ (CtxD CtxR TyR) (TyPreD TyPreR ,×TmUR)) (λ _ → ⊤) 
                           (λ TmPreR _ ΓA → TmPreD ,×Π×wkR TmPreR ΓA)

TmPre ,×Π×wkR Γ A = Fix (λ a b c → TmPreD ,×Π×wkR a c) 
                        ⦃ TmPreD-PreFunctor {,×Π×wkR = ,×Π×wkR} ⦄ (Γ Σ, A)

Ty Γ = TyPre (unfix Γ)

Tm Γ A = TmPre {,×TmUR = fixInterpret} 
               (λ Δ B → (fix Δ , fix B) Σ, (λ C → Π (fix B) (fix C)) 
                                        Σ, (λ C → wk (fix B) (fix C))) 
               (unfix Γ) (unfix A)
 