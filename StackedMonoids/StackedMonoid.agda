{-# OPTIONS --universe-polymorphism #-}
module StackedMonoids.StackedMonoid where

open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Relation.Binary

open import Level

import Algebra.FunctionProperties as FP

record StackedMonoid c ℓ (n : ℕ) : Set (suc (c ⊔ ℓ)) where
  field
    universe : Setoid c ℓ
  
  open Setoid universe renaming (Carrier to X ; _≈_ to ≈)
  open FP ≈

  field
    id       : Fin n → X 
    op       : Fin n → Op₂ X 
    assoc    : (x : Fin n) → Associative (op x) 
    identity : (x : Fin n) → Identity (id x) (op x)
    cong     : (x : Fin n) → (op x) Preserves₂ ≈ ⟶ ≈ ⟶ ≈ 

  open Setoid universe public renaming (Carrier to X)
