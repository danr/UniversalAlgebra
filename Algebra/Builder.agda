{-# OPTIONS --universe-polymorphism #-}
open import Data.List renaming (map to listMap)
open import Data.Nat hiding (_⊔_)

module Algebra.Builder (arities : List ℕ) where

open import Data.Nat.Comparison-Properties
open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality renaming (setoid to Set→Setoid)
open import Data.Fin renaming (_<_ to _<Fin_ ; _≤_ to _≤Fin_)
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function
open import Data.ParallelVector
open import Data.ParallelList
open import Data.SimpleN-ary

ops : ℕ
ops = length arities

α : Vec ℕ ops
α = fromList arities

data Expr (v : ℕ) : Set where
  var : (x : Fin v) → Expr v
  op  : (x : Fin ops) (args : Vec (Expr v) (lookup x α)) → Expr v

data Equality (v : ℕ) : Set where
  _==_ : (lhs rhs : Expr v) → Equality v

Env : (v n : ℕ) → Set
Env v n = Vec (Expr v) n

law-type : (v n : ℕ) → Set₁
law-type v zero    = Set
law-type v (suc n) = Expr v → law-type v n

law-run′ : (v n : ℕ) → law-type v n
law-run′ v zero    = Equality v
law-run′ v (suc n) = λ i → law-run′ v n

law-∀ : (v n : ℕ) → law-type v n → Set
law-∀ v zero    P = P
law-∀ v (suc n) P = (x : Expr v) → law-∀ v n (P x)

law-run″ : (v n : ℕ) → Env v n → law-∀ v n (law-run′ v n) → Equality v
law-run″ v zero    Γ        = λ xs → xs
law-run″ v (suc n) (x ∷ xs) = λ f → law-run″ v n xs (f x)

law-run : (v : ℕ) → law-∀ v v (law-run′ v v) → Equality v
law-run v = law-run″ v v (Data.Vec.map var (allFin v))

-- Arity of an operator, indexed by a comparison
arity : ∀ {n} → n < ops → ℕ
arity p = lookup (fromℕ≤ p) α

-- The underlying type
type : (n : ℕ) (p : n ≤ ops) → Set₁
type zero    p = Set 
type (suc n) p = (∀ {v} → Op (arity p) (Expr v)) → (type n (↓ p)) 
 
-- Quantification over the type
∀′ : (n : ℕ) (p : n ≤ ops) → type n p → Set
∀′ zero    p P = P
∀′ (suc n) p P = (op : ({v : ℕ} → Op (arity p) (Expr v))) → ∀′ n (↓ p) (P op)

-- The runner type
run-type : (n : ℕ) (p : n ≤ ops) → type n p
run-type zero    p = List (∃ λ v → (law-∀ v v (law-run′ v v)))
run-type (suc n) p = λ f → run-type n (↓ p) 

-- Runner
run : (n : ℕ) (p : n ≤ ops) → ∀′ n p (run-type n p) → List (∃ Equality) 
run zero    p = λ xs → Data.List.map (λ x → proj₁ x , law-run (proj₁ x) (proj₂ x) ) xs
run (suc n) p = λ f → run n (↓ p) (f (λ {v} → makeOp (arity p) (op {v} (fromℕ≤ p))))

-- To build, start from the beginning
build : ∀′ ops m≤m (run-type ops m≤m) → List (∃ Equality)
build = run ops m≤m

module Interpret c ℓ (setoid : Setoid c ℓ) 
                     (⟦op_⟧ : (x : Fin ops) → Op (lookup x α) (Setoid.Carrier setoid)) where
  open Setoid setoid renaming (Carrier to X)

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

  ⟦_⟧ : ∀ {n} → ShadowExpr n → Vec X n → ShadowExpr 0
  ⟦ elem x      ⟧ [] = elem x
  ⟦ (var ())    ⟧ []
  ⟦ (op x args) ⟧ [] = op x args
  ⟦ e           ⟧ (x ∷ xs) = ⟦ replace e x ⟧ xs

  mutual 
    ξ : ∀ {m} → Vec (ShadowExpr 0) m → Vec X m
    ξ []       = []
    ξ (e ∷ es) = interpret e ∷ ξ es

    interpret : ShadowExpr 0 → X
    interpret (elem x) = x
    interpret (var ())
    interpret (op x args) = apply (lookup x α) ⟦op x ⟧ (ξ args)
    
  ⟦_⟧′ : ∀ {n} → Equality n → N-ary n X (Set ℓ)
  ⟦ lhs == rhs ⟧′ = curryⁿ λ Γ → interpret (⟦ shadow lhs ⟧ Γ) ≈ interpret (⟦ shadow rhs ⟧ Γ) 

--
-- Need to put the vector in an environment to be able to do a function
-- that lowers Equality at the same time as the environment to be able
-- to ∀ over it. Too much coding for now to figure out how to do it. 
--  

{-
  ⟦_⟧′ : ∀ {n} → Equality n → Vec X n → Set ℓ
  ⟦ lhs == rhs ⟧′ Γ = ⟦ lhs ⟧ Γ ≈ ⟦ rhs ⟧ Γ

  ⟦_⟧″ : ∀ {n} → Equality n → N-ary n X (Set ℓ)
  ⟦ eq ⟧″ = curryⁿ ⟦ eq ⟧′

  ∀⟦_⟧ : ∀ {n} {m} → (eq : Equality n) → ∀ⁿ m ⟦ eq ⟧″
  ∀⟦_⟧ {zero}  eq = {!!}
  ∀⟦_⟧ {suc n} eq = λ x → {!∀⟦_⟧ {n} x!}
-}