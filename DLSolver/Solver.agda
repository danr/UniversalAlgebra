{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Solver {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.Fin
open import Data.Nat
open import Data.Product renaming (map to _⋆_)
open import Data.Vec 
open import Data.List hiding (and ; or)

open import Function

open import DLSolver.VarSets
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import Algebra.Props.DistributiveLattice as P-DL; open P-DL DL
import DLSolver.Eval         as Eval;        open Eval DL
import DLSolver.DNF-Correct  as DNF-Correct; open DNF-Correct DL
import DLSolver.DNF-Sort     as Sort;        open Sort DL
import DLSolver.Redundancies as Red;         open Red DL

import Relation.Binary.Reflection as Reflection

NF : ∀ {n} (e : Expr n) → Meets n
NF = sort ∘ removeRedundancies ∘ DNF

NF-correct : ∀ {n} (e : Expr n) (Γ : Env n) → ⟦ e ⟧ Γ ≈ ⟦ NF e ⟧′ Γ
NF-correct e Γ = DNF-correct Γ e 
               ⟨ trans ⟩ rmReds-correct Γ (DNF e) 
               ⟨ trans ⟩ sort-correct Γ (removeRedundancies (DNF e))

open Reflection setoid var ⟦_⟧ (λ e Γ → ⟦ NF e ⟧′ Γ) (λ e Γ → sym (NF-correct e Γ))
  public renaming (_⊜_ to _:=_)

-- Some examples
private
  
  ex₁ : ∀ x y z → x ∧ (y ∧ z) ≈ (z ∧ y) ∧ (x ∧ z)
  ex₁ = solve 3 (λ x y z → x and (y and z) := (z and y) and (x and z)) refl
  
  ex₂ : ∀ a b c d → (a ∧ b) ∧ (c ∧ d) 
                  ≈ (a ∧ c) ∧ (b ∧ d)
  ex₂ = solve 4 (λ a b c d → (a and b) and (c and d) 
                          := (a and c) and (b and d)) refl
  
  ex₃ : ∀ x y z → x ∨ y ∨ z ≈ y ∨ x ∨ z
  ex₃ = solve 3 (λ x y z → x or y or z := y or x or z) refl
  
  -- General distributivity
  ex₄ : ∀ x y z → (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x) ≈ (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x) 
  ex₄ = solve 3 (λ x y z → (x and y) or (y and z) or (z and x) 
                        := (x and y) or (y and z) or (z and x)) refl
  
  -- Modular
  ex₅ : ∀ a b x → (x ∧ b) ∨ (a ∧ b) ≈ ((x ∧ b) ∨ a) ∧ b
  ex₅ = solve 3 (λ a b x → (x and b) or (a and b)
                        := ((x and b) or a) and b) refl
