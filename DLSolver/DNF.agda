module DLSolver.DNF where

open import Data.Nat
open import Data.Fin
open import Data.List.NonEmpty 
open import DLSolver.VarSets
open import Category.Monad
open RawMonad monad

infixr 8 _and_
infixr 7 _or_

-- The expression datatype  
data Expr (n : ℕ) : Set where
  var        : (x : Fin n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

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
