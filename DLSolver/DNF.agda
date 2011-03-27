module DLSolver.DNF where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_) 
open import Data.List.NonEmpty renaming (monad to monad⁺)
open import DLSolver.VarSets
open import Category.Monad

open RawMonad monad⁺

infixr 8 _and_
infixr 7 _or_
  
data Expr (n : ℕ) : Set where
  var        : (x : Fin n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

DNF : ∀ {n} → Expr n → Meets n
DNF (var x)     = [ singleton x ]
DNF (e₁ or  e₂) = DNF e₁ ⁺++⁺ DNF e₂  
DNF (e₁ and e₂) = DNF e₁ >>= λ t₁ → DNF e₂ >>= λ t₂ → [ t₁ ∪ t₂ ]
