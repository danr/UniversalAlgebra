{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.Eval {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List.NonEmpty renaming (monad to monad⁺)
open import DLSolver.VarSets
open import DLSolver.DNF
open import Category.Monad
open import Function

open DistributiveLattice DL renaming (Carrier to X)

Env : ℕ → Set δ₁
Env n = Vec X n

⟦_⟧ : ∀ {n} → Expr n → Env n → X
⟦ var x     ⟧ Γ = lookup x Γ
⟦ e₁ and e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∧ ⟦ e₂ ⟧ Γ
⟦ e₁ or e₂  ⟧ Γ = ⟦ e₁ ⟧ Γ ∨ ⟦ e₂ ⟧ Γ

⟦_⟧″ : ∀ {n} → VS n → Env n → X
⟦ true∷ vs  ⟧″ (γ ∷ Γ) = γ ∧ ⟦ vs ⟧″ Γ
⟦ false∷ vs ⟧″ (γ ∷ Γ) =     ⟦ vs ⟧″ Γ
⟦ lastTrue  ⟧″ (γ ∷ Γ) = γ

⟦_⟧′ : ∀ {n} → Meets n → Env n → X
⟦ [ M ]  ⟧′ Γ = ⟦ M ⟧″ Γ
⟦ M ∷ Ms ⟧′ Γ = ⟦ M ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ
