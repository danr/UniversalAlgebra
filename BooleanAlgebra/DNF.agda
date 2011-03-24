{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.DNF where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Maybe
open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import Category.Monad
open import Function

open RawMonad []-monad
  
data Expr (n : ℕ) : Set where
  var        : (x : Fin n) → Expr n
  top bottom : Expr n
  neg        : (e : Expr n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

DNF : ∀ {n} → Expr n → Meets n
DNF (var x)     = [ singleton x ]
DNF top         = [ replicate F ]
DNF bottom      = []
DNF (neg e)     = map (V-map not) (DNF e)
DNF (e₁ or  e₂) = DNF e₁ ++ DNF e₂  
DNF (e₁ and e₂) = DNF e₁ >>= λ t₁ → DNF e₂ >>= λ t₂ → maybeToList (t₁ ∩ t₂)
