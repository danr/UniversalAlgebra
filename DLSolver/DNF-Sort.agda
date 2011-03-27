{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.DNF-Sort {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.Nat hiding (_≤?_)
open import Data.Fin hiding (compare)
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate ; [_])
open import Data.List.NonEmpty
open import Data.Product hiding (map)

open import Function

open import Relation.Nullary
open import Relation.Binary

open import DLSolver.VarSets
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import DLSolver.Eval as Eval; open Eval DL
import DLSolver.Lemmas as Lemmas; open Lemmas DL

insert : ∀ {n} → VS n → Meets n → Meets n
insert M′ [ M ]    with VStoList M′ ≤? VStoList M
... | yes p = M  ∷ [ M′ ]
... | no ¬p = M′ ∷ [ M ]
insert M′ (M ∷ Ms) with VStoList M′ ≤? VStoList M 
... | yes p = M  ∷ insert M′ Ms
... | no ¬p = M′ ∷ M ∷ Ms 

sort : ∀ {n} → Meets n → Meets n
sort [ M ]    = [ M ]
sort (M ∷ Ms) = insert M (sort Ms) 

insert-correct : ∀ {n} (Γ : Env n) v vs
               → ⟦ v ⟧″ Γ ∨ ⟦ vs ⟧′ Γ ≈ ⟦ insert v vs ⟧′ Γ
insert-correct Γ M′ [ M ] with VStoList M′ ≤? VStoList M
... | yes p = ∨-comm _ _
... | no ¬p = refl
insert-correct Γ M′ (M ∷ Ms) with VStoList M′ ≤? VStoList M
... | yes p = lemma₆ 
            ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ insert-correct Γ M′ Ms)
... | no ¬p = refl

sort-correct : ∀ {n} (Γ : Env n) vs
             → ⟦ vs ⟧′ Γ ≈ ⟦ sort vs ⟧′ Γ
sort-correct Γ [ M ]    = refl
sort-correct Γ (M ∷ Ms) = refl ⟨ ∨-cong ⟩ sort-correct Γ Ms 
                        ⟨ trans ⟩ insert-correct Γ M (sort Ms)