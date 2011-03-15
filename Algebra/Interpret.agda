{-# OPTIONS --universe-polymorphism #-}
open import Relation.Binary
open import Data.List
open import Data.ParallelList hiding (_++_)
open import Data.Nat hiding (_⊔_)
open import Data.SimpleN-ary

module Algebra.Interpret 
  (arities : List ℕ)
  c ℓ (setoid : Setoid c ℓ) 
  (operators : ParList (λ n → Op n (Setoid.Carrier setoid)) arities)
  where

open Setoid setoid renaming (Carrier to X)

open import Data.Vec hiding (_++_)
open import Data.ParallelVector
open import Data.Fin
open import Data.Vec.Pi-ary
open import Level

import Algebra.Builder as Builder
open Builder arities

private

  ⟦op_⟧ : (x : Fin ops) → Op (lookup x α) X
  ⟦op_⟧ = par-lookup (fromParList operators)
   
  data ShadowExpr (v : ℕ) : Set c where
    elem : (x : X) → ShadowExpr v
    var  : (x : Fin v) → ShadowExpr v
    op   : (x : Fin ops) (args : Vec (ShadowExpr v) (lookup x α)) → ShadowExpr v
   
  -- Termination checker rewritage
  mutual
    ψ : ∀ {n m} → Vec (Expr n) m → Vec (ShadowExpr n) m
    ψ []       = []
    ψ (e ∷ es) = shadow e ∷ ψ es
   
    shadow : ∀ {n} → Expr n → ShadowExpr n
    shadow (var x) = var x
    shadow (op x args) = op x (ψ args)
   
  mutual
    ζ : ∀ {n m} → Vec (ShadowExpr (suc n)) m → X → Vec (ShadowExpr n) m
    ζ []       v = []
    ζ (e ∷ es) v = replace e v ∷ ζ es v
   
    replace : ∀ {n} → ShadowExpr (suc n) → X → ShadowExpr n 
    replace (elem x)      v = elem x
    replace (var zero)    v = elem v
    replace (var (suc x)) v = var x
    replace (op x args)   v = op x (ζ args v)
   
  mutual 
    ξ : ∀ {m} → Vec (ShadowExpr 0) m → Vec X m
    ξ []       = []
    ξ (e ∷ es) = interpret e ∷ ξ es
   
    interpret : ShadowExpr 0 → X
    interpret (elem x) = x
    interpret (var ())
    interpret (op x args) = apply (lookup x α) ⟦op x ⟧ (ξ args)
   
  open import Data.Product
   
  data Env (n : ℕ) : Set c where
    _,_ : (l r : ShadowExpr n) → Env n
   
  ⟦_⟧′ : ∀ {n} → Env n → N-ary n X (Set ℓ)
  ⟦_⟧′ {zero}        (lhs , rhs) = interpret lhs ≈ interpret rhs
  ⟦_⟧′ {suc zero}    (lhs , rhs) = λ x → ⟦ replace lhs x , replace rhs x ⟧′
  ⟦_⟧′ {suc (suc n)} (lhs , rhs) = λ x → ⟦ replace lhs x , replace rhs x ⟧′
   
  level : (n : ℕ) → Level
  level zero    = ℓ
  level (suc n) = ℓ ⊔ c
   
  ∀ⁿ′ : (n : ℕ) → N-ary n X (Set ℓ) → Set (level n)
  ∀ⁿ′ zero          P = P 
  ∀ⁿ′ (suc zero)    P = ∀ x → ∀ⁿ′ zero (P x) 
  ∀ⁿ′ (suc (suc n)) P = ∀ x → ∀ⁿ′ (suc n) (P x)
   
⟦_⟧ : ∀ {n} → Equality n → Set (ℓ ⊔ c)
⟦_⟧ {n} (lhs == rhs) = ∀ⁿ′ (suc n) ⟦ shadow lhs , shadow rhs ⟧′

private   
   
  double : ℕ → ℕ
  double zero    = zero
  double (suc n) = suc (suc (double n))
   
  equals : List (X × X) → Set ℓ → Set ℓ
  equals []              t = t                    -- this case will never happen
  equals ((x , x′) ∷ []) t = x ≈ x′ → t
  equals ((x , x′) ∷ xs) t = x ≈ x′ → equals xs t
   
  congruence : ∀ n → List (X × X) → Op n X → Op n X → N-ary (double n) X (Set ℓ)
  congruence zero          xs x y = equals xs (x ≈ y)
  congruence (suc zero)    xs f g = λ x y → congruence zero    (xs ++ (x , y) ∷ []) (f x) (g y)
  congruence (suc (suc n)) xs f g = λ x y → congruence (suc n) (xs ++ (x , y) ∷ []) (f x) (g y)
   
   
  ∀ⁿʰ′ : (n : ℕ) → N-ary n X (Set ℓ) → Set (level n)
  ∀ⁿʰ′ zero          P = P 
  ∀ⁿʰ′ (suc zero)    P = ∀ {x} → ∀ⁿʰ′ zero (P x) 
  ∀ⁿʰ′ (suc (suc n)) P = ∀ {x} → ∀ⁿʰ′ (suc n) (P x)
   
  congr : ∀ n → Op (suc n) X → Set (ℓ ⊔ c)
  congr n f = ∀ⁿʰ′ (double (suc n)) (congruence (suc n) [] f f) 
   
  open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl)
  open import Data.Empty
   
congr≢ : ∀ n → n ≢ 0 → Op n X → Set (ℓ ⊔ c)
congr≢ zero eq = ⊥-elim (eq ≡-refl)
congr≢ (suc n) eq = congr n