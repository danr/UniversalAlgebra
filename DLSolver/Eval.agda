{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Eval {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.Nat
open import Data.Vec using (Vec ; lookup ; _∷_)
open import Data.List.NonEmpty 

open import DLSolver.VarSets
open import DLSolver.DNF
open import DLSolver.Expr

open DistributiveLattice DL renaming (Carrier to X)

-- The environment, mapping each variable to an actual element in the universe
Env : ℕ → Set δ₁
Env n = Vec X n

-- Evaluating an expression to a value
⟦_⟧ : ∀ {n} → Expr n → Env n → X
⟦ var x     ⟧ Γ = lookup x Γ
⟦ e₁ and e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∧ ⟦ e₂ ⟧ Γ
⟦ e₁ or e₂  ⟧ Γ = ⟦ e₁ ⟧ Γ ∨ ⟦ e₂ ⟧ Γ

-- Evaluating a variable set to a value. 
-- Here the construction with lastTrue is crucial.
⟦_⟧″ : ∀ {n} → VS n → Env n → X
⟦ true∷ vs  ⟧″ (γ ∷ Γ) = γ ∧ ⟦ vs ⟧″ Γ
⟦ false∷ vs ⟧″ (γ ∷ Γ) =     ⟦ vs ⟧″ Γ
⟦ lastTrue  ⟧″ (γ ∷ Γ) = γ

-- Evaluating a formula in DNF to a value.
⟦_⟧′ : ∀ {n} → DNF n → Env n → X
⟦ [ M ]  ⟧′ Γ = ⟦ M ⟧″ Γ
⟦ M ∷ Ms ⟧′ Γ = ⟦ M ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ
