{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Solver {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Function

open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import Algebra.Props.DistributiveLattice as P-DL; open P-DL DL
import DLSolver.Eval         as Eval;        open Eval DL
import DLSolver.DNF-Correct  as DNF-Correct; open DNF-Correct DL
import DLSolver.DNF-Sort     as Sort;        open Sort DL
import DLSolver.Redundancies as Red;         open Red DL

import Relation.Binary.Reflection as Reflection

------------------------------------------------------------------------
-- The normal form is a sorted, irredundant DNF

NF : ∀ {n} (e : Expr n) → DNF n
NF = sort ∘ removeRedundancies ∘ toDNF

NF-correct : ∀ {n} (e : Expr n) (Γ : Env n) → ⟦ NF e ⟧′ Γ ≈ ⟦ e ⟧ Γ
NF-correct e Γ = sym (toDNF-correct Γ e ⟨ trans ⟩ 
                      rmReds-correct Γ (toDNF e) ⟨ trans ⟩ 
                      sort-correct Γ (removeRedundancies (toDNF e)))

------------------------------------------------------------------------
-- Opening the reflection primitives

open Reflection setoid var ⟦_⟧ (λ e Γ → ⟦ NF e ⟧′ Γ) (λ e Γ → NF-correct e Γ)
  public renaming (_⊜_ to _:=_)

------------------------------------------------------------------------
-- Some examples
private
  
  -- General distributivity
  ex₁ : ∀ x y z → (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x) ≈ (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x) 
  ex₁ = solve 3 (λ x y z → (x and y) or (y and z) or (z and x) 
                        := (x and y) or (y and z) or (z and x)) refl
  
  -- Modular law
  ex₂ : ∀ a b x → (x ∧ b) ∨ (a ∧ b) ≈ ((x ∧ b) ∨ a) ∧ b
  ex₂ = solve 3 (λ a b x → (x and b) or (a and b)
                        := ((x and b) or a) and b) refl

  -- Testing the redundancy remover a little
  ex₃ : ∀ x y z → x ∨ (x ∧ y) ∨ (x ∧ z) ∨ (x ∧ y ∧ z) ∨ (y ∧ z) ≈ x ∨ (y ∧ z)
  ex₃ = solve 3 (λ x y z → x or (x and y) or (x and z) or (x and y and z) or (y and z) 
                        := x or (y and z)) refl

  -- Takes about a minute to type check on my computer
  ex₄ : ∀ x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ 
      → (x₁ ∨ y₁) ∧ (x₂ ∨ y₂) ∧ (x₃ ∨ y₃) ∧ (x₄ ∨ y₄) ∧ (x₅ ∨ y₅)
      ≈ (x₃ ∨ y₃) ∧ (x₄ ∨ y₄) ∧ (x₅ ∨ y₅) ∧ (x₁ ∨ y₁) ∧ (x₂ ∨ y₂) 
  ex₄ = solve 10 (λ x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
           → (x₁ or y₁) and (x₂ or y₂) and (x₃ or y₃) and (x₄ or y₄) and (x₅ or y₅)
          := (x₃ or y₃) and (x₄ or y₄) and (x₅ or y₅) and (x₁ or y₁) and (x₂ or y₂)) refl