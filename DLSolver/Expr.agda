module DLSolver.Expr where

open import Data.Nat
open import Data.Fin

infixr 8 _and_
infixr 7 _or_

-- The expression datatype  
data Expr (n : ℕ) : Set where
  var        : (x : Fin n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

