-----------------
--
-- Work in progress!!
--
-----------------

{-# OPTIONS --universe-polymorphism #-}
module Algebra.Menu where

import Algebra.Builder as Builder

open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality renaming (setoid to Set→Setoid)
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Fin renaming (_<_ to _<Fin_ ; _≤_ to _≤Fin_)
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function
open import Data.ParallelVector
open import Data.ParallelList
open import Data.SimpleN-ary

import Data.Vec.Pi-ary as Pi
import Algebra.Interpret as Interpret

record Structure : Set where
  field 
    arities   : List ℕ 

  open Builder arities

  field 
    laws      : List (∃ Equality) 

  open Builder arities public

NonZero : (xs : List ℕ) → List (∃ λ n → n ≢ 0)
NonZero [] = []
NonZero (zero ∷ xs) = NonZero xs
NonZero (suc n ∷ xs) = (suc n , λ ()) ∷ NonZero xs

ParNonZero : ∀ {i} {B : ℕ → Set i} (xs : List ℕ) → ParList B xs → ParList (λ x → B (proj₁ x)) (NonZero xs)
ParNonZero [] [] = []
ParNonZero (zero  ∷ xs) (p ∷ ps) = ParNonZero xs ps
ParNonZero (suc n ∷ xs) (p ∷ ps) = p ∷ ParNonZero xs ps

record Instance c ℓ (S : Structure) : Set (suc (ℓ ⊔ c)) where
  open Structure S 

  field
    setoid : Setoid c ℓ

  open Setoid setoid renaming (Carrier to X)
  
  field
    ⟦op⟧ : ParList (λ n → Op n X) arities

  open Interpret arities c ℓ setoid ⟦op⟧

  ⟦op⁺⟧ : ParList (λ n → Op (proj₁ n) X) (NonZero arities)
  ⟦op⁺⟧ = ParNonZero arities ⟦op⟧

  -- Need pattern matching on record constructors!
  field
    ⟦law⟧ : ParList (λ x → ⟦ proj₂ x ⟧) laws
    ⟦cong⟧ : ParList (λ x → congr≢ (proj₁ (proj₁ x)) (proj₂ (proj₁ x)) (proj₂ x)) (toFlatList ⟦op⁺⟧)


module ImplicitBuilder {arities : List ℕ} where
  open Builder arities public using (build ; Expr ; Equality ; _==_)

open ImplicitBuilder public

-- Sketch of projection formulas
{-
module Projection {c ℓ} {S : Structure} (I : Instance c ℓ S) where

  open Structure S
  open Instance I

  c₀ : {0 ∈ arities} → Carrier
  c₀ {here} = ...
  
  c₁ : {0 ∈₂ arities} → Carrier

  _+_ bin₀ _∙_ : {2 ∈ arities} → Op 2 Carrier

  _*_ bin₁     : {2 ∈₂ arities} → Op 2 Carrier

  -_ _⁻¹ : {1 ∈ arities} → Op 1 Carrier

  if_then_else_ _⟨_⟩_ _?_∶_   -- i don't know any used ternary operators really ^^

  law : (n : ℕ) → {p : n < #laws} → ∀ⁿ x (Law (lookup (fromℕ p) arities))
  
  assoc assoc-+ assoc₀ : {p : Associative ∈̂ laws} → ...

  -- given a concrete structure and an instance, these implicit arguments
  -- can be automatically inferred (oh shit, actually they probably can't)
  -- maybe only the < one or maybe not even that one... hmm
  -- but I guess if you write a decision procedure! and pattern matches
  -- on that it returns yes instead. hmm. that's probably it.
-}

