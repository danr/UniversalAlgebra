module Algebra.Test where

open import Algebra.Instance 
open import Algebra.Menu
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Data.List
open import Data.ParallelList

ℤ-Ring : Instance zero zero Ring
ℤ-Ring = record
  { setoid = setoid ℤ
  ; ⟦op⟧   = _*_ ∷ _+_ ∷ -_ ∷ (+ 1) ∷ (+ 0) ∷ []
  ; ⟦law⟧  = {!!} 
           ∷ {!!} 
           ∷ {!!} 
           ∷ {!!} 
           ∷ {!!} 
           ∷ {!!}
           ∷ {!!}
           ∷ {!!}
           ∷ {!!}
           ∷ {!!}
           ∷ {!!} 
           ∷ []
  ; ⟦cong⟧ = (λ eq eq′ → cong₂ _*_ eq eq′) 
           ∷ {!!} 
           ∷ {!!} 
           ∷ []
  }
