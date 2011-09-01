{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.DNF-Correct {β₁ β₂} (DL : DistributiveLattice β₁ β₂) where

open import Data.Fin
open import Data.Vec using (_∷_ ; [])
open import Data.Product using (proj₁ ; proj₂)
open import Data.List.NonEmpty 

open import Category.Monad
open RawMonad monad

open import Function

open import DLSolver.VarSets
open import DLSolver.Expr
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import DLSolver.Eval as Eval; open Eval DL
import DLSolver.Lemmas as Lemmas; open Lemmas DL

------------------------------------------------------------------------
-- Variables

var-homomorphic : ∀ {n} (Γ : Env n) (x : Fin n) → ⟦ var x ⟧ Γ ≈ ⟦ toDNF (var x) ⟧′ Γ
var-homomorphic [] ()
var-homomorphic (γ ∷ Γ) zero    = refl
var-homomorphic (γ ∷ Γ) (suc x) = var-homomorphic Γ x                                    

------------------------------------------------------------------------
-- Expressions with or. Corresponds to a list append.

++-homomorphic : ∀ {n} (Γ : Env n) (ms ms′ : DNF n) → ⟦ ms ⟧′ Γ ∨ ⟦ ms′ ⟧′ Γ ≈ ⟦ ms ⁺++⁺ ms′ ⟧′ Γ
++-homomorphic Γ [ m ]    ms′ = refl
++-homomorphic Γ (m ∷ ms) ms′ = ∨-assoc (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) (⟦ ms′ ⟧′ Γ) ⟨ trans ⟩ 
                                (refl ⟨ ∨-cong ⟩ ++-homomorphic Γ ms ms′)

------------------------------------------------------------------------
-- Expressions with and are a bit more involved, due to the cartesian-
-- product-like distributivity

∩-homomorphic : ∀ {n} (Γ : Env n) (vs vs′ : VS n) → ⟦ vs ∪ vs′ ⟧″ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
∩-homomorphic []      ()          ()
∩-homomorphic (γ ∷ Γ) (true∷ vs)  (true∷ vs′)  = lemma₂ (∩-homomorphic Γ vs vs′)
∩-homomorphic (γ ∷ Γ) (true∷ vs)  (false∷ vs′) = refl ⟨ ∧-cong ⟩ ∩-homomorphic Γ vs vs′ ⟨ trans ⟩ 
                                                 sym (∧-assoc _ _ _)
∩-homomorphic (γ ∷ Γ) (true∷ vs)  lastTrue     = lemma₃ 
∩-homomorphic (γ ∷ Γ) (false∷ vs) (true∷ vs′)  = lemma₁ (∩-homomorphic Γ vs vs′)
∩-homomorphic (γ ∷ Γ) (false∷ vs) (false∷ vs′) = ∩-homomorphic Γ vs vs′
∩-homomorphic (γ ∷ Γ) (false∷ vs) lastTrue     = ∧-comm _ _
∩-homomorphic (γ ∷ Γ) lastTrue    (true∷ vs′)  = lemma₀
∩-homomorphic (γ ∷ Γ) lastTrue    (false∷ vs′) = refl
∩-homomorphic (γ ∷ Γ) lastTrue    lastTrue     = sym (∧-idempotent γ)
  
and-homomorphic′ : ∀ {n} (Γ : Env n) (m : VS n) (ms : DNF n)
                → ⟦ m ⟧″ Γ ∧ ⟦ ms ⟧′ Γ
                ≈ ⟦ (ms >>= λ m′ → [ m ∪ m′ ]) ⟧′ Γ
and-homomorphic′ Γ m [ m′ ]    = sym (∩-homomorphic Γ m m′) 
and-homomorphic′ Γ m (m′ ∷ ms) = proj₁ ∧-∨-distrib (⟦ m ⟧″ Γ) (⟦ m′ ⟧″ Γ) (⟦ ms ⟧′ Γ) ⟨ trans ⟩ 
                                 (sym (∩-homomorphic Γ m m′) ⟨ ∨-cong ⟩ and-homomorphic′ Γ m ms) ⟨ trans ⟩ 
                                 ++-homomorphic Γ [ m ∪ m′ ] (ms >>= λ m′ → [ m ∪ m′ ]) 
  
and-homomorphic : ∀ {n} (Γ : Env n) (ms ms′ : DNF n)
             → ⟦ ms ⟧′ Γ ∧ ⟦ ms′ ⟧′ Γ 
             ≈ ⟦ (ms >>= λ m → ms′ >>= λ m′ → [ m ∪ m′ ]) ⟧′ Γ
and-homomorphic Γ [ m ]    ms′ = and-homomorphic′ Γ m ms′
and-homomorphic Γ (m ∷ ms) ms′ = proj₂ ∧-∨-distrib (⟦ ms′ ⟧′ Γ) (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) ⟨ trans ⟩ 
                                 (and-homomorphic′ Γ m ms′ ⟨ ∨-cong ⟩ and-homomorphic Γ ms ms′) ⟨ trans ⟩ 
                                 ++-homomorphic Γ (ms′ >>= λ m′ → [ m ∪ m′ ]) 
                                                  (ms >>= λ m → ms′ >>= λ m′ → [ m ∪ m′ ])

------------------------------------------------------------------------
-- Transformation to DNF preserves the value of the evaluated expression

toDNF-correct : ∀ {n} (Γ : Env n) (e : Expr n) → ⟦ e ⟧ Γ ≈ ⟦ toDNF e ⟧′ Γ
toDNF-correct Γ (var x)     = var-homomorphic Γ x
toDNF-correct Γ (e₁ and e₂) = toDNF-correct Γ e₁ ⟨ ∧-cong ⟩ toDNF-correct Γ e₂ ⟨ trans ⟩ 
                              and-homomorphic Γ (toDNF e₁) (toDNF e₂)
toDNF-correct Γ (e₁ or e₂)  = toDNF-correct Γ e₁ ⟨ ∨-cong ⟩ toDNF-correct Γ e₂ ⟨ trans ⟩ 
                              ++-homomorphic Γ (toDNF e₁) (toDNF e₂)
