{-# OPTIONS --universe-polymorphism #-}
open import Data.List renaming (map to listMap)
open import Data.Nat hiding (_⊔_)

module Algebra.Builder (arities : List ℕ) where

open import Data.Nat.Comparison-Properties
open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality renaming (setoid to Set→Setoid)
open import Data.Fin renaming (_<_ to _<Fin_ ; _≤_ to _≤Fin_ ; pred to Fin-pred)
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
  _==_ : (lhs rhs : Expr (suc v)) → Equality v

private
  Env : (v n : ℕ) → Set
  Env v n = Vec (Expr (suc v)) n
   
  law-type : (v n : ℕ) → Set₁
  law-type v zero    = Set
  law-type v (suc n) = Expr (suc v) → law-type v n
   
  law-run′ : (v n : ℕ) → law-type v n
  law-run′ v zero    = Equality v
  law-run′ v (suc n) = λ i → law-run′ v n
   
  law-∀ : (v n : ℕ) → law-type v n → Set
  law-∀ v zero    P = P
  law-∀ v (suc n) P = (x : Expr (suc v)) → law-∀ v n (P x)
   
  law-run″ : (v n : ℕ) → Env v n → law-∀ v n (law-run′ v n) → Equality v
  law-run″ v zero    Γ        = λ xs → xs
  law-run″ v (suc n) (x ∷ xs) = λ f → law-run″ v n xs (f x)
   
  law-run : (v : ℕ) → law-∀ v (suc v) (law-run′ v (suc v)) → Equality v
  law-run v = law-run″ v (suc v) (Data.Vec.map var (allFin (suc v)))
   
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
   
  run-type zero    p = List (∃ λ v → (law-∀ v (suc v) (law-run′ v (suc v))))
  run-type (suc n) p = λ f → run-type n (↓ p) 
   
  -- Runner
  run : (n : ℕ) (p : n ≤ ops) → ∀′ n p (run-type n p) → List (∃ Equality) 
  run zero    p = λ xs → Data.List.map (λ x → (proj₁ x) , law-run  (proj₁ x) (proj₂ x ) ) xs
  run (suc n) p = λ f → run n (↓ p) (f (λ {v} → makeOp (arity p) (op {v} (fromℕ≤ p))))
   
-- To build, start from the beginning
build : ∀′ ops m≤m (run-type ops m≤m) → List (∃ Equality)
build = run ops m≤m
   
