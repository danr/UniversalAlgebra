module Algebra.Test where

open import Algebra.Instance 
open import Algebra.Menu
open import Level renaming (zero to Level-zero)
open import Relation.Binary.PropositionalEquality hiding (setoid ; refl)
open import Data.List
open import Data.ParallelList

open import Data.Product

open import Data.Nat using (ℕ ; _*_ ; _+_)
open import Data.Nat.Properties
import Algebra as Alg

open Alg.CommutativeSemiring commutativeSemiring hiding (_*_ ; _+_)

ℕ-Ring : Instance Level-zero Level-zero CommutativeSemiring
ℕ-Ring = record
  { setoid = setoid
  ; ⟦op⟧   = _*_ ∷ _+_ ∷ 1 ∷ 0 ∷ []
  ; ⟦law⟧  = +-assoc
           ∷ proj₂ +-identity 
           ∷ proj₁ +-identity
           ∷ +-comm 
           ∷ *-assoc
           ∷ proj₂ *-identity 
           ∷ proj₁ *-identity 
           ∷ *-comm 
           ∷ proj₁ distrib
           ∷ (λ x y z → proj₂ distrib z x y)
           ∷ proj₂ zero
           ∷ proj₁ zero
           ∷ []
  ; ⟦cong⟧ = (λ eq eq′ → *-cong eq eq′)  -- skapa en egen cons 
           ∷ (λ eq eq′ → +-cong eq eq′)
           ∷ []
  }
