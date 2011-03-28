{-# OPTIONS --universe-polymorphism #-}
module DLSolver.VarSets where

open import Data.Nat using (ℕ ; suc) 
open import Data.Vec using (Vec ; _∷_ ; replicate ; toList) 
open import Data.Fin using (Fin ; suc ; zero) 
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺) 
open import Data.Bool
open import Data.Bool.StrictTotalOrder

open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.List.StrictLex as Lex

infixr 5 true∷_ false∷_
infix 4 _∪_ _⊆_ _⊆?_ _⊈_

------------------------------------------------------------------------
-- Variable sets.
-- Basically a Vec Bool, but at least one true.

data VS : ℕ → Set where
  true∷_   : ∀ {n} (vs : VS n) → VS (suc n)
  false∷_  : ∀ {n} (vs : VS n) → VS (suc n)
  lastTrue : ∀ {n} → VS (suc n)

-- The singleton set
singleton : ∀ {n} → Fin n → VS n
singleton zero    = lastTrue
singleton (suc n) = false∷ singleton n

-- Union
_∪_ : ∀ {n} → VS n → VS n → VS n
true∷ vs  ∪ true∷ vs′  = true∷ (vs ∪ vs′)
true∷ vs  ∪ false∷ vs′ = true∷ (vs ∪ vs′)
true∷ vs  ∪ lastTrue   = true∷ vs
false∷ vs ∪ true∷ vs′  = true∷ (vs ∪ vs′)
false∷ vs ∪ false∷ vs′ = false∷ (vs ∪ vs′)
false∷ vs ∪ lastTrue   = true∷ vs
lastTrue  ∪ true∷  vs′ = true∷ vs′
lastTrue  ∪ false∷ vs′ = true∷ vs′
lastTrue  ∪ lastTrue   = lastTrue

------------------------------------------------------------------------
-- Subsets of variable sets

data _⊆_ : ∀ {n} → VS n → VS n → Set where
  last   : ∀ {n}                                     → lastTrue ⊆ lastTrue {n}
  stop   : ∀ {n}                 (vs′ : VS n)        → lastTrue ⊆ true∷ vs′
  keep   : ∀ {n} {vs vs′ : VS n} (vs⊆vs′ : vs ⊆ vs′) → true∷  vs ⊆ true∷  vs′
  drop-T : ∀ {n} {vs vs′ : VS n} (vs⊆vs′ : vs ⊆ vs′) → false∷ vs ⊆ true∷  vs′
  drop-F : ∀ {n} {vs vs′ : VS n} (vs⊆vs′ : vs ⊆ vs′) → false∷ vs ⊆ false∷ vs′

_⊈_ : ∀ {n} → VS n → VS n → Set
A ⊈ B = ¬ A ⊆ B

------------------------------------------------------------------------
-- Subset is decidable

⊆-keep-tail : ∀ {n} {vs vs′ : VS n} → true∷ vs ⊆ true∷ vs′ → vs ⊆ vs′
⊆-keep-tail (keep vs⊆vs′) = vs⊆vs′

⊆-drop-T-tail : ∀ {n} {vs vs′ : VS n} → false∷ vs ⊆ true∷ vs′ → vs ⊆ vs′
⊆-drop-T-tail (drop-T vs⊆vs′) = vs⊆vs′

⊆-drop-F-tail : ∀ {n} {vs vs′ : VS n} → false∷ vs ⊆ false∷ vs′ → vs ⊆ vs′
⊆-drop-F-tail (drop-F vs⊆vs′) = vs⊆vs′

_⊆?_ : ∀ {n} → Decidable (_⊆_ {n})
true∷ vs ⊆? true∷ vs′ with vs ⊆? vs′
... | yes p = yes (keep p)
... | no ¬p = no (¬p ∘ ⊆-keep-tail)
true∷ vs ⊆? false∷ vs′ = no (λ ())
true∷ vs ⊆? lastTrue = no (λ ())
false∷ vs ⊆? true∷ vs′ with vs ⊆? vs′
... | yes p = yes (drop-T p)
... | no ¬p = no (¬p ∘ ⊆-drop-T-tail)
false∷ vs ⊆? false∷ vs′ with vs ⊆? vs′
... | yes p = yes (drop-F p)
... | no ¬p = no (¬p ∘ ⊆-drop-F-tail)
false∷ vs ⊆? lastTrue = no (λ ())
lastTrue ⊆? true∷ vs = yes (stop vs)
lastTrue ⊆? false∷ vs = no (λ ())
lastTrue ⊆? lastTrue = yes last

------------------------------------------------------------------------
-- For sorting

VStoVec : ∀ {n} → VS n → Vec Bool n
VStoVec (true∷ vs)  = true  ∷ VStoVec vs
VStoVec (false∷ vs) = false ∷ VStoVec vs
VStoVec lastTrue    = true  ∷ replicate false

VStoList : ∀ {n} → VS n → List Bool
VStoList = toList ∘ VStoVec

VB-DecTotalOrder : DecTotalOrder _ _ _
VB-DecTotalOrder = ≤-decTotalOrder BoolStrictTotalOrder

open DecTotalOrder VB-DecTotalOrder public using (_≤?_)
