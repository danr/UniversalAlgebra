module DLSolver.DNF where

open import Data.Nat
open import Data.Fin
open import Data.List.NonEmpty 
open import DLSolver.VarSets
open import DLSolver.Expr
open import Category.Monad
open RawMonad monad

------------------------------------------------------------------------
-- The DNF is a non-empty list of variable sets.
-- [ M₁ , M₂ , .. , Mn ] to be interpreted as
-- M₁ ∨ M₂ ∨ .. ∨ Mn,
-- and each Mi is a variable set to be interpreted as x₀ⁱ ∧ .. ∧ xnⁱ

DNF : ℕ → Set
DNF n = List⁺ (VS n)

-- Translating an expression to DNF
toDNF : ∀ {n} → Expr n → DNF n
toDNF (var x)     = [ singleton x ]
toDNF (e₁ or  e₂) = toDNF e₁ ⁺++⁺ toDNF e₂  
toDNF (e₁ and e₂) = toDNF e₁ >>= λ m₁ → toDNF e₂ >>= λ m₂ → [ m₁ ∪ m₂ ]
