{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.DNF-Correct {β₁ β₂} (DL : DistributiveLattice β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate ; [_]) renaming (monad to []-monad)
open import Data.Product hiding (map)
open import Data.List.NonEmpty hiding (SnocView) renaming (monad to monad⁺) 

open import Category.Monad

open RawMonad monad⁺

open import Function

open import DLSolver.VarSets
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import DLSolver.Eval as Eval; open Eval DL
import DLSolver.Lemmas as Lemmas; open Lemmas DL

var-homomorphic : ∀ {n} (Γ : Env n) (x : Fin n) → ⟦ var x ⟧ Γ ≈ ⟦ DNF (var x) ⟧′ Γ
var-homomorphic [] ()
var-homomorphic (γ ∷ Γ) zero    = refl
var-homomorphic (γ ∷ Γ) (suc x) = var-homomorphic Γ x                                    

++-homomorphic : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n) → ⟦ m₁ ⟧′ Γ ∨ ⟦ m₂ ⟧′ Γ ≈ ⟦ m₁ ⁺++⁺ m₂ ⟧′ Γ
++-homomorphic Γ [ m ]    ms′ = refl
++-homomorphic Γ (m ∷ ms) ms′ = ∨-assoc (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) (⟦ ms′ ⟧′ Γ) 
                   ⟨ trans ⟩ ∨-cong (refl {⟦ m ⟧″ Γ}) (++-homomorphic Γ ms ms′)

∩-homomorphic : ∀ {n} (Γ : Env n) (vs vs′ : VS n) → ⟦ vs ∪ vs′ ⟧″ Γ ≈ ⟦ vs ⟧″ Γ ∧ ⟦ vs′ ⟧″ Γ
∩-homomorphic []      ()          ()
∩-homomorphic (γ ∷ Γ) (true∷ vs)  (true∷ vs′)  = lemma₇ (∩-homomorphic Γ vs vs′)
∩-homomorphic (γ ∷ Γ) (true∷ vs)  (false∷ vs′) = refl ⟨ ∧-cong ⟩ ∩-homomorphic Γ vs vs′ ⟨ trans ⟩ sym (∧-assoc _ _ _)
∩-homomorphic (γ ∷ Γ) (true∷ vs)  lastTrue     = lemma₂
∩-homomorphic (γ ∷ Γ) (false∷ vs) (true∷ vs′)  = lemma₃ (∩-homomorphic Γ vs vs′)
∩-homomorphic (γ ∷ Γ) (false∷ vs) (false∷ vs′) = ∩-homomorphic Γ vs vs′
∩-homomorphic (γ ∷ Γ) (false∷ vs) lastTrue     = ∧-comm _ _
∩-homomorphic (γ ∷ Γ) lastTrue    (true∷ vs′)  = lemma₀
∩-homomorphic (γ ∷ Γ) lastTrue    (false∷ vs′) = refl
∩-homomorphic (γ ∷ Γ) lastTrue    lastTrue     = sym (∧-idempotent γ)
  
and′-homomorphic : ∀ {n} (Γ : Env n) (m : VS n) (ms : Meets n) 
                → ⟦ m ⟧″ Γ ∧ ⟦ ms ⟧′ Γ
                ≈ ⟦ (ms >>= λ t → [ m ∪ t ]) ⟧′ Γ
and′-homomorphic Γ m [ m′ ]    = sym (∩-homomorphic Γ m m′) 
and′-homomorphic Γ m (m′ ∷ ms) = proj₁ ∧-∨-distrib (⟦ m ⟧″ Γ) (⟦ m′ ⟧″ Γ) (⟦ ms ⟧′ Γ)  
                              ⟨ trans ⟩ (sym (∩-homomorphic Γ m m′) ⟨ ∨-cong ⟩ and′-homomorphic Γ m ms)
                              ⟨ trans ⟩ ++-homomorphic Γ [ m ∪ m′ ]
                                                      (ms >>= λ t → [ m ∪ t ]) 
  
and-homomorphic : ∀ {n} (Γ : Env n) (m₁ m₂ : Meets n)
             → ⟦ m₁ ⟧′ Γ ∧ ⟦ m₂ ⟧′ Γ 
             ≈ ⟦ (m₁ >>= λ t₁ → m₂ >>= λ t₂ → [ t₁ ∪ t₂ ]) ⟧′ Γ
and-homomorphic Γ [ m ]    m₂ = and′-homomorphic Γ m m₂
and-homomorphic Γ (m ∷ ms) m₂ = proj₂ ∧-∨-distrib (⟦ m₂ ⟧′ Γ) (⟦ m ⟧″ Γ) (⟦ ms ⟧′ Γ) 
                           ⟨ trans ⟩ (and′-homomorphic Γ m m₂ ⟨ ∨-cong ⟩ and-homomorphic Γ ms m₂) 
                           ⟨ trans ⟩ ++-homomorphic Γ (m₂ >>= λ t → [ m ∪ t ]) 
                                                   (ms >>= λ t₁ → m₂ >>= λ t₂ → [ t₁ ∪ t₂ ])


DNF-correct : ∀ {n} (Γ : Env n) (e : Expr n) → ⟦ e ⟧ Γ ≈ ⟦ DNF e ⟧′ Γ
DNF-correct Γ (var x)     = var-homomorphic Γ x
DNF-correct Γ (e₁ and e₂) = ∧-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ and-homomorphic Γ (DNF e₁) (DNF e₂)
DNF-correct Γ (e₁ or e₂)  = ∨-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ ++-homomorphic Γ (DNF e₁) (DNF e₂)
