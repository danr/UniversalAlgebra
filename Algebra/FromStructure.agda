open import Algebra.Menu
open import Data.List
open import Data.Nat

module Algebra.FromStructure {arities : List ℕ} (From′ : Structure) where

import Algebra.Builder as Builder

open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality renaming (setoid to Set→Setoid)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Comparison-Properties
open import Data.Fin renaming (_<_ to _<Fin_ ; _≤_ to _≤Fin_)
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function
open import Data.ParallelVector
open import Data.ParallelList
open import Data.SimpleN-ary

import Algebra.Interpret as Interpret

module From = Structure From′
module To = Builder arities

-- Code copy from Builder :(

private
    
  applySubst : ParList (λ n → (∀ v → Vec (To.Expr v) n → To.Expr v)) (From.arities) → List (∃ To.Equality)
  applySubst li = Data.List.map conv From.laws
    where
      mutual
        ϕ : {n m : ℕ} → Vec (From.Expr n) m → Vec (To.Expr n) m
        ϕ [] = []
        ϕ (x ∷ xs) = conv′ x ∷ ϕ xs
   
        conv′ : {n : ℕ} → From.Expr n → To.Expr n
        conv′ {n} (Builder.var x) = Builder.var x
        conv′ {n} (Builder.op x args) = par-lookup (fromParList li) x n (ϕ args) 
   
      conv : ∃ From.Equality → ∃ To.Equality
      conv (n , Builder._==_ lhs rhs) = n , Builder._==_ (conv′ lhs) (conv′ rhs)

  ops : ℕ
  ops = length arities

  α : Vec ℕ ops
  α = fromList arities

  -- Arity of an operator, indexed by a comparison
  arity : ∀ {n} → n < ops → ℕ
  arity p = lookup (fromℕ≤ p) α
   
  -- The underlying type
  type : (n : ℕ) (p : n ≤ ops) → Set₁
  type zero    p = Set 
  type (suc n) p = (∀ v → Vec (To.Expr v) (arity p) → To.Expr v) → (type n (↓ p)) 
   
  -- Quantification over the type
  ∀′ : (n : ℕ) (p : n ≤ ops) → type n p → Set
  ∀′ zero    p P = P
  ∀′ (suc n) p P = (op : (∀ v → Vec (Expr v) (arity p) → To.Expr v)) → ∀′ n (↓ p) (P op)
   
  -- The runner type
  run-type : (n : ℕ) (p : n ≤ ops) → type n p
  run-type zero    p = ParList (λ n → (∀ v → Vec (To.Expr v) n → To.Expr v)) (From.arities) 
  run-type (suc n) p = λ f → run-type n (↓ p) 
   
  -- Runner
  run : (n : ℕ) (p : n ≤ ops) → ∀′ n p (run-type n p) → List (∃ To.Equality) 
  run zero    p = λ xs → applySubst xs 
  run (suc n) p = λ f → run n (↓ p) (f (λ v xs → Builder.op {_} {v} (fromℕ≤ p) xs)) 
   
-- To build, start from the beginning
from⟨_⟩ : ∀′ ops m≤m (run-type ops m≤m) → List (∃ To.Equality)
from⟨_⟩ = run ops m≤m