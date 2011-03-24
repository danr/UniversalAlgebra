{-# OPTIONS --universe-polymorphism #-}
open import Algebra

module BooleanAlgebra.DNF-Sort {β₁ β₂} (BA : BooleanAlgebra β₁ β₂) where

open import Data.Nat hiding (compare)
open import Data.Fin hiding (compare)
open import Data.Vec hiding ([_] ; _>>=_ ; _++_ ; foldr) renaming (map to V-map)
open import Data.List hiding (replicate) renaming (monad to []-monad)
open import Data.Product hiding (map)

open import Function

open import Relation.Binary

open import BooleanAlgebra.Member
open import BooleanAlgebra.VarSets
open import BooleanAlgebra.DNF

open BooleanAlgebra BA renaming (Carrier to X)
import BooleanAlgebra.Eval as Eval; open Eval BA
import BooleanAlgebra.Lemmas as Lemmas; open Lemmas BA

insert : ∀ {n} → VS n → Meets n → Meets n
insert M′ [] = [ M′ ] 
insert M′ (M ∷ Ms) with compare (toList M′) (toList M)
... | tri> _ _ _ = M ∷ insert M′ Ms
... | _          = M′ ∷ M ∷ Ms 

sort : ∀ {n} → Meets n → Meets n
sort []       = []
sort (M ∷ Ms) = insert M (sort Ms) 

insert-correct : ∀ {n} (Γ : Env n) v vs
               → ⟦ v ⟧″ Γ ∨ ⟦ vs ⟧′ Γ ≈ ⟦ insert v vs ⟧′ Γ
insert-correct Γ M  []       = refl
insert-correct Γ M′ (M ∷ Ms) with compare (toList M′) (toList M)
... | tri> _ _ _ = sym (∨-assoc _ _ _) 
                 ⟨ trans ⟩ (∨-comm _ _ ⟨ ∨-cong ⟩ refl) 
                 ⟨ trans ⟩ (∨-assoc _ _ _) 
                 ⟨ trans ⟩ (refl {⟦ M ⟧″ Γ} ⟨ ∨-cong ⟩ insert-correct Γ M′ Ms)
... | tri≈ _ _ _ = refl
... | tri< _ _ _ = refl

sort-correct : ∀ {n} (Γ : Env n) vs
             → ⟦ vs ⟧′ Γ ≈ ⟦ sort vs ⟧′ Γ
sort-correct Γ []       = refl
sort-correct Γ (M ∷ Ms) = refl ⟨ ∨-cong ⟩ sort-correct Γ Ms 
                        ⟨ trans ⟩ insert-correct Γ M (sort Ms)