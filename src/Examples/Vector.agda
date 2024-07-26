{-# OPTIONS --without-K --rewriting #-}

open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ℕ_)
open import Function using (_∘_; case_of_)
open import Data.Product using (Σ; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
  renaming (trans to _∙_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift)

open import Indexed
open import IndexedUtils
open import Utils

module Examples.Vector where

module _ (A : Set) where
  VecD : (ℕ → Set) → ℕ → Set
  VecD vec n = (n ≡ 0) + Σ ℕ (λ m → A × vec m × n ≡ suc m)

instance
  VecD-Functor : ∀ {A} → Functor _ (VecD A)
VecD-Functor .All P (inl p) = Lift _ ⊤
VecD-Functor .All P (inr (n , x , xs , p)) = P n xs
VecD-Functor .all P p (inl q) = lift tt
VecD-Functor .all P p (inr (n , x , xs , q)) = p xs
VecD-Functor .collect (inl p) (lift tt) = inl p
VecD-Functor .collect (inr (n , x , xs , p)) q = inr (n , x , (xs , q) , p)
VecD-Functor .discard (inl p) = inl p
VecD-Functor .discard (inr (n , x , (xs , q) , p)) = inr (n , x , q , p)

VecD-Functor .discard-coh (inl _) = refl
VecD-Functor .discard-coh (inr _) = refl
VecD-Functor .collect-fst (inl _) _ = refl
VecD-Functor .collect-fst (inr _) _ = refl
VecD-Functor .fmap-id (inl _) = refl
VecD-Functor .fmap-id (inr _) = refl
VecD-Functor .fmap-comp f g (inl _) = refl
VecD-Functor .fmap-comp f g (inr _) = refl

Vec : Set → ℕ → Set
Vec A = Fix (VecD A)

pattern [] = inl refl
pattern _∷_ x xs = inr (_ , x , xs , refl)

vecElim : ∀ {A} (P : ∀ i → Vec A i → Set) 
        → P _ (fix []) → (∀ {i} x xs → P i xs → P _ (fix (x ∷ xs)))
        → ∀ {i} xs → P i xs
vecElim P P[] P∷ xs = Fix-elim P (λ where 
  [] (lift tt) → P[]
  (x ∷ xs) ps → P∷ x xs ps) xs

take : ∀ {A} m {n} → Vec A (m +ℕ n) → Vec A m
take zero xs = fix []
take (suc m) xs = case unfix xs of λ where (x ∷ xs) → fix (x ∷ take m xs)

drop : ∀ {A} m {n} → Vec A (m +ℕ n) → Vec A n
drop zero xs = xs
drop (suc m) xs = case unfix xs of λ where (x ∷ xs) → drop m xs

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m +ℕ n)
_++_ {A} {m} {n} xs ys 
  = Fix-fold {A = Vec A ∘ (_+ℕ n)} (λ where [] → ys; (x ∷ xs) → fix (x ∷ xs)) xs

take++drop≡id : ∀ {A} m {n} (xs : Vec A (m +ℕ n)) → take m xs ++ drop m xs ≡ xs
take++drop≡id zero xs = refl
take++drop≡id (suc m) xs = case unfix≡ xs of λ where 
  ((x ∷ xs) , refl) → cong (λ xs′ → fix (x ∷ xs′)) (take++drop≡id m xs)
