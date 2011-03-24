{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.Eval {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Maybe
open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF
open import Category.Monad
open import Function

open BooleanAlgebra BA renaming (Carrier to X)

Env : ℕ → Set β₁
Env n = Vec X n

⟦_⟧ : ∀ {n} → Expr n → Env n → X
⟦ var x     ⟧ Γ = lookup x Γ
⟦ top       ⟧ Γ = ⊤
⟦ bottom    ⟧ Γ = ⊥
⟦ neg e     ⟧ Γ = ⟦ e ⟧ (V-map ¬_ Γ)
⟦ e₁ and e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∧ ⟦ e₂ ⟧ Γ
⟦ e₁ or e₂  ⟧ Γ = ⟦ e₁ ⟧ Γ ∨ ⟦ e₂ ⟧ Γ

⟦_⟧v : Member → X → X
⟦_⟧v T γ =   γ
⟦_⟧v N γ = ¬ γ
⟦_⟧v F γ =   ⊤

⟦_⟧″ : ∀ {n} → VS n → Env n → X
⟦ []     ⟧″ []      = ⊤
⟦ x ∷ xs ⟧″ (γ ∷ Γ) = ⟦ x ⟧v γ ∧ ⟦ xs ⟧″ Γ

⟦_⟧′ : ∀ {n} → Meets n → Env n → X
⟦ []     ⟧′ Γ = ⊥
⟦ M ∷ Ms ⟧′ Γ = ⟦ M ⟧″ Γ ∨ ⟦ Ms ⟧′ Γ
