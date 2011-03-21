{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module LatticeSolver.LatticeSolver {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where



open import Data.Nat
open import Data.Fin
open import Data.Bool renaming (_∨_ to _⋁_ ; _∧_ to _⋀_)
open import Data.List hiding ([_])
open import Data.List.NonEmpty hiding (head ; tail) renaming (monad to List⁺-monad)
open import Data.Maybe renaming (monadPlus to Maybe-monadPlus)
open import Data.Vec hiding (_>>=_ ; [_])
open import Function
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
open import Level renaming (zero to z)

open import Category.Monad


import Algebra.Props.DistributiveLattice as DL-Props
open DistributiveLattice DL renaming (Carrier to X ; isEquivalence to isEqDL)
open DL-Props DL

open import LatticeSolver.VariableSets

infixr 5 _and_
infixr 4 _or_

data Expr (n : ℕ) : Set where
  var    : (x : Fin n) → Expr n
  _and_ _or_ : (e₁ e₂ : Expr n) → Expr n

DNF : ∀ {n} → Expr n → Meets₁ n
DNF (var x)     = [ singleton x ]
DNF (e₁ or  e₂) = union (DNF e₁) (DNF e₂)
DNF (e₁ and e₂) = DNF e₁ >>= λ t₁ → DNF e₂ >>= λ t₂ → [ t₁ ∪ t₂ ] 
  where open RawMonad List⁺-monad


Env : ℕ → Set δ₁
Env n = Vec X n

⟦_⟧ : ∀ {n} → Expr n → Env n → X
⟦ var x     ⟧ Γ = lookup x Γ
⟦ e₁ and e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ ∧ ⟦ e₂ ⟧ Γ
⟦ e₁ or e₂  ⟧ Γ = ⟦ e₁ ⟧ Γ ∨ ⟦ e₂ ⟧ Γ

module Eval-Meet where

  -- this is going to be messy

  open RawMonadPlus (Maybe-monadPlus {δ₁})

  ⟦_⟧″ : ∀ {n} → VS n → Env n → Maybe X
  ⟦_⟧″ []           Γ = nothing
  ⟦_⟧″ (true ∷ xs)  Γ = maybe (λ x → (head Γ) ∧ x) (just (head Γ)) (⟦ xs ⟧″ (tail Γ))
  ⟦_⟧″ (false ∷ xs) Γ = ⟦ xs ⟧″ (tail Γ)

  ⟦_⟧₁ : ∀ {n} → VS₁ n → Env n → X
  ⟦_⟧₁ (true∷  xs) Γ = maybe (λ x → head Γ ∧ x) (just (head Γ)) (⟦ xs ⟧″ (tail Γ))
  ⟦_⟧₁ (false∷ xs) Γ = ⟦ xs ⟧₁ (tail Γ)

open Eval-Meet

⟦_⟧′ : ∀ {n} → Meets₁ n → Env n → X
⟦_⟧′ [ M ]    Γ = ⟦ M ⟧₁ Γ
⟦_⟧′ (M ∷ Ms) Γ = ⟦ M ⟧₁ Γ ∨ ⟦ Ms ⟧′ Γ