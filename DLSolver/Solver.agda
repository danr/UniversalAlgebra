{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Solver {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Function

open import DLSolver.DNF
open import DLSolver.Expr public

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

open Reflection setoid var ⟦_⟧ (λ e Γ → ⟦ NF e ⟧′ Γ) NF-correct
  public renaming (_⊜_ to _:=_)

