module Algebra.Instance where

open import Algebra.Menu

--Right now we need _∷_ from all of these. That needs to change :)

open import Data.List
open import Data.Fin
open import Data.Vec
open import Data.ParallelVector
open import Data.ParallelList
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

import Algebra.FunctionProperties as FP

Group : Structure
Group = record 
  { arities = 2 ∷ 1 ∷ 0 ∷ []
  ; laws = build 
         (λ ε _⁻¹ _∙_ → (2 , λ x y z → ((x ∙ y) ∙ z) == (x ∙ (y ∙ z))) 
                      ∷ {!!}
                      ∷ {!!}
                      ∷ {!!}
                      ∷ {!!}
                      ∷ []) 
  }

-- A Lava is a Magma that is commutative
-- PS. I made this up
Lava : Structure
Lava = record 
  { arities = 2 ∷ []
  ; laws    = build (λ _∙_ → (1 , λ x y → (x ∙ y) == (y ∙ x)) ∷ [])
  }

data ℤ₂ : Set where
  #0 #1 : ℤ₂

_+′_ : ℤ₂ → ℤ₂ → ℤ₂
#0 +′ #0 = #0
#1 +′ #0 = #1
#0 +′ #1 = #1
#1 +′ #1 = #0

+-comm : ∀ x y → x +′ y ≡ y +′ x
+-comm #0 #0 = refl
+-comm #0 #1 = refl
+-comm #1 #0 = refl
+-comm #1 #1 = refl

open import Data.Sum

ℤ₂-Lava : Instance zero zero Lava
ℤ₂-Lava = record 
  { setoid = setoid ℤ₂
  ; ⟦op⟧   = _+′_ ∷ []
  ; ⟦law⟧  = (λ x y → +-comm x y) ∷ []
  ; ⟦cong⟧ = inj₂ (λ {ne} {x} → cong₂ _+′_ {x}) ∷ []
  }

Commutativity : ∀ x y → x +′ y ≡ y +′ x
Commutativity = par-lookup (fromParList (Instance.⟦law⟧ ℤ₂-Lava)) zero


