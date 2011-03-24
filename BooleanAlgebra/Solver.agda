{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Solver {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Fin
open import Data.Nat
open import Data.Product 
open import Data.Vec 
open import Data.List hiding (and ; or)

open import Function

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import Algebra.Props.BooleanAlgebra as P-BA; open P-BA BA
import BooleanAlgebra.Eval         as Eval;        open Eval BA
import BooleanAlgebra.DNF-Correct  as DNF-Correct; open DNF-Correct BA
import BooleanAlgebra.DNF-Sort     as Sort;        open Sort BA
import BooleanAlgebra.Redundancies as Red;         open Red BA

import Relation.Binary.Reflection as Reflection

NF : ∀ {n} (e : Expr n) → Meets n
NF = sort ∘ removeRedundancies ∘ DNF

NF-correct : ∀ {n} (e : Expr n) (Γ : Env n) → ⟦ e ⟧ Γ ≈ ⟦ NF e ⟧′ Γ
NF-correct e Γ = DNF-correct Γ e 
               ⟨ trans ⟩ rmReds-correct Γ (DNF e) 
               ⟨ trans ⟩ sort-correct Γ (removeRedundancies (DNF e))

open Reflection setoid var ⟦_⟧ (λ e Γ → ⟦ NF e ⟧′ Γ) (λ e Γ → sym (NF-correct e Γ))
  public renaming (_⊜_ to _:=_)


ex₁ : ∀ x → ¬ ¬ x ≈ x
ex₁ = solve 1 (λ x → neg (neg x) := x) refl

ex₂ : ∀ x y z → x ∧ (y ∧ z) ≈ (z ∧ y) ∧ (x ∧ z)
ex₂ = solve 3 (λ x y z → x and (y and z) := (z and y) and (x and z)) refl

-- Broken!
-- ¬ x ∨ ¬ y has two normal forms
-- [ [ N , N ] ] and
-- [ [ N , F ] , [ F , N ] ]

-- ex₃ : ∀ x y → (¬ x) ∧ (¬ y) ≈ ¬ (x ∨ y)
-- ex₃ = solve 2 (λ x y → (neg x) and (neg y) := neg (x or y)) refl

rhs : Meets 2
rhs = NF ((neg (var (# 0))) and (neg (var (# 1))))

lhs : Meets 2
lhs = NF (neg (var (# 0) or var (# 1)))

