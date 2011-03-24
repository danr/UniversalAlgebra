{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.DNF-Correct {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Product hiding (map)

open import Function

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import BooleanAlgebra.Eval as Eval; open Eval BA
import BooleanAlgebra.HomomorphicAnd as And; open And BA
import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA

var-homomorphic : ∀ {n} (Γ : Env n) (x : Fin n) → ⟦ var x ⟧ Γ ≈ ⟦ DNF (var x) ⟧′ Γ
var-homomorphic [] ()
var-homomorphic (γ ∷ [])     zero    = sym (proj₂ C.∧-identity γ) ⟨ trans ⟩
                                    sym (proj₂ C.∨-identity (γ ∧ ⊤))
var-homomorphic (γ ∷ γ′ ∷ Γ) zero    = var-homomorphic (γ ∷ Γ) zero ⟨ trans ⟩ 
                                    (refl {γ} ⟨ ∧-cong ⟩ sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 
var-homomorphic (γ ∷ Γ)      (suc x) = var-homomorphic Γ x ⟨ trans ⟩ 
                                    (sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 

top-homomorphic : ∀ {n} (Γ : Env n) → ⟦ top ⟧ Γ ≈ ⟦ DNF top ⟧′ Γ
top-homomorphic []      = sym (proj₂ C.∨-identity ⊤)
top-homomorphic (γ ∷ Γ) = top-homomorphic Γ ⟨ trans ⟩ 
                       (sym (proj₁ C.∧-identity _) ⟨ ∨-cong ⟩ refl {⊥}) 

neg′-homomorphic : ∀ {n} (Γ : Env n) (vs : VS n) → ⟦ vs ⟧″ (V-map ¬_ Γ) ≈ ⟦ V-map not vs ⟧″ Γ
neg′-homomorphic []      []       = refl
neg′-homomorphic (γ ∷ Γ) (T ∷ vs) = refl {¬ γ}     ⟨ ∧-cong ⟩ neg′-homomorphic Γ vs
neg′-homomorphic (γ ∷ Γ) (N ∷ vs) = ¬-involutive γ ⟨ ∧-cong ⟩ neg′-homomorphic Γ vs
neg′-homomorphic (γ ∷ Γ) (F ∷ vs) = refl {⊤}       ⟨ ∧-cong ⟩ neg′-homomorphic Γ vs 

neg-homomorphic : ∀ {n} (Γ : Env n) (m : Meets n) → ⟦ m ⟧′ (V-map ¬_ Γ) ≈ ⟦ map (V-map not) m ⟧′ Γ
neg-homomorphic Γ []       = refl
neg-homomorphic Γ (m ∷ ms) = neg′-homomorphic Γ m ⟨ ∨-cong ⟩ neg-homomorphic Γ ms


DNF-correct : ∀ {n} (Γ : Env n) (e : Expr n) → ⟦ e ⟧ Γ ≈ ⟦ DNF e ⟧′ Γ
DNF-correct Γ (var x)     = var-homomorphic Γ x
DNF-correct Γ top         = top-homomorphic Γ
DNF-correct Γ bottom      = refl
DNF-correct Γ (neg e)     = DNF-correct (V-map ¬_ Γ) e ⟨ trans ⟩ neg-homomorphic Γ (DNF e)
DNF-correct Γ (e₁ and e₂) = ∧-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ and-homomorphic Γ (DNF e₁) (DNF e₂)
DNF-correct Γ (e₁ or e₂)  = ∨-cong (DNF-correct Γ e₁) (DNF-correct Γ e₂) 
                          ⟨ trans ⟩ ++-homomorphic Γ (DNF e₁) (DNF e₂)
