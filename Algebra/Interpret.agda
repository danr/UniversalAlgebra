{-# OPTIONS --universe-polymorphism #-}
open import Relation.Binary
open import Data.List
open import Data.ParallelList
open import Data.Nat hiding (_⊔_)
open import Data.SimpleN-ary

module Algebra.Interpret 
  (arities : List ℕ)
  c ℓ (setoid : Setoid c ℓ) 
  (operators : ParList (λ n → Op n (Setoid.Carrier setoid)) arities)
  where

open Setoid setoid renaming (Carrier to X)

open import Data.Vec
open import Data.ParallelVector
open import Data.Fin
open import Data.Vec.N-ary
open import Level

import Algebra.Builder as Builder
open Builder arities

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

{-

⟦_⟧ : ∀ {n} → ShadowExpr n → Vec X n → ShadowExpr 0
⟦ elem x      ⟧ [] = elem x
⟦ (var ())    ⟧ []
⟦ (op x args) ⟧ [] = op x args
⟦ e           ⟧ (x ∷ xs) = ⟦ replace e x ⟧ xs

-}

mutual 
  ξ : ∀ {m} → Vec (ShadowExpr 0) m → Vec X m
  ξ []       = []
  ξ (e ∷ es) = interpret e ∷ ξ es

  interpret : ShadowExpr 0 → X
  interpret (elem x) = x
  interpret (var ())
  interpret (op x args) = apply (lookup x α) ⟦op x ⟧ (ξ args)
  
{-

⟦_⟧′ : ∀ {n} → Equality n → N-ary n X (Set ℓ)
⟦ lhs == rhs ⟧′ = curryⁿ λ Γ → interpret (⟦ shadow lhs ⟧ Γ) ≈ interpret (⟦ shadow rhs ⟧ Γ) 

-}

open import Data.Product

data Env (n : ℕ) : Set c where
  _,_ : (l r : ShadowExpr n) → Env n

run′ : (n : ℕ) → N-ary n X (Set (suc ℓ))
run′ zero    = Set ℓ
run′ (suc n) = λ x → run′ n

run″ : (n : ℕ) → Env n → ∀ⁿ n (run′ n)
run″ zero    (l , r) = interpret l ≈ interpret r
run″ (suc n) (l , r) = λ x → run″ n (replace l x , replace r x)

⟦_⟧ : {n : ℕ} → Equality n → ∀ⁿ n (run′ n)
⟦_⟧ {n} (lhs == rhs) = run″ n (shadow lhs , shadow rhs)


{-

 Need to put the vector in an environment to be able to do a function
 that lowers Equality at the same time as the environment to be able
 to ∀ over it. Too much coding for now to figure out how to do it. 
  


⟦_⟧′ : ∀ {n} → Equality n → Vec X n → Set ℓ
⟦ lhs == rhs ⟧′ Γ = ⟦ lhs ⟧ Γ ≈ ⟦ rhs ⟧ Γ

⟦_⟧″ : ∀ {n} → Equality n → N-ary n X (Set ℓ)
⟦ eq ⟧″ = curryⁿ ⟦ eq ⟧′

∀⟦_⟧ : ∀ {n} {m} → (eq : Equality n) → ∀ⁿ m ⟦ eq ⟧″
∀⟦_⟧ {zero}  eq = {!!}
∀⟦_⟧ {suc n} eq = λ x → {!∀⟦_⟧ {n} x!}

-}