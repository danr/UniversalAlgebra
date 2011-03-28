{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module DLSolver.DNF-Sort {δ₁ δ₂} (DL : DistributiveLattice δ₁ δ₂) where

open import Data.List.NonEmpty
open import Function
open import Relation.Nullary

open import DLSolver.VarSets
open import DLSolver.DNF

open DistributiveLattice DL renaming (Carrier to X)
import DLSolver.Eval as Eval; open Eval DL
import DLSolver.Lemmas as Lemmas; open Lemmas DL

------------------------------------------------------------------------
-- Insertion sorting the DNF to make normal forms set equivalent.
-- Notice that it is not proved that this insertion sort actually sorts 
-- the list, though I think it would be necessary to prove completeness.

insert : ∀ {n} → VS n → DNF n → DNF n
insert m′ [ m ]    with VStoList m′ ≤? VStoList m
... | yes p = m  ∷ [ m′ ]
... | no ¬p = m′ ∷ [ m ]
insert m′ (m ∷ ms) with VStoList m′ ≤? VStoList m 
... | yes p = m  ∷ insert m′ ms
... | no ¬p = m′ ∷ m ∷ ms 

sort : ∀ {n} → DNF n → DNF n
sort [ m ]    = [ m ]
sort (m ∷ ms) = insert m (sort ms) 

------------------------------------------------------------------------
-- Sorting the DNF still yields the same value

insert-correct : ∀ {n} (Γ : Env n) (m′ : VS n) (ms : DNF n)
               → ⟦ m′ ⟧″ Γ ∨ ⟦ ms ⟧′ Γ ≈ ⟦ insert m′ ms ⟧′ Γ
insert-correct Γ m′ [ m ] with VStoList m′ ≤? VStoList m
... | yes p = ∨-comm _ _
... | no ¬p = refl
insert-correct Γ m′ (m ∷ ms) with VStoList m′ ≤? VStoList m
... | yes p = lemma₆ ⟨ trans ⟩ (refl ⟨ ∨-cong ⟩ insert-correct Γ m′ ms)
... | no ¬p = refl

sort-correct : ∀ {n} (Γ : Env n) (ms : DNF n)
             → ⟦ ms ⟧′ Γ ≈ ⟦ sort ms ⟧′ Γ
sort-correct Γ [ m ]    = refl
sort-correct Γ (m ∷ ms) = refl ⟨ ∨-cong ⟩ sort-correct Γ ms ⟨ trans ⟩ 
                          insert-correct Γ m (sort ms)