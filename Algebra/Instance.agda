module Algebra.Instance where

open import Algebra.Menu

--Right now we need _∷_ from all of these. That needs to change :)

open import Data.List
open import Data.Fin
open import Data.Vec
open import Data.ParallelVector
open import Data.ParallelList

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

-- A Lava is a Magma that is commutative
-- PS. I made this up
Lava : Structure
Lava = record 
  { arities   = 2 ∷ []
  ; arguments = 2 ∷ []
  ; laws      = Builder._==_ (Builder.op zero (Builder.var zero       ∷ Builder.var (suc zero) ∷ []))
                             (Builder.op zero (Builder.var (suc zero) ∷ Builder.var zero       ∷ [])) 
              ∷ [] 
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

-- Want to instantiating in a more convenient way.
-- Maybe have a hidden instantiating record, and an open one that you sort
-- of run a function to to convert it
-- I think it might be a good idea to have the datatype abstract,
-- then I can for instance sort the operators/laws how I wish
ℤ₂-Lava : Instance zero zero Lava
ℤ₂-Lava = record 
  { setoid = setoid ℤ₂
  ; ⟦op⟧   = _+′_ ∷ []
  ; ⟦law⟧  = (λ xs → +-comm (lookup zero xs) (lookup (suc zero) xs)) ∷ []
  }

-- Cannot do uncurry on this one (loses dependency information somehow)
-- Uncurry this in the interpretation instead (trickier, but doable)
Commutativity : ∀ x y → x +′ y ≡ y +′ x
Commutativity x y = par-lookup (Instance.⟦law⟧ ℤ₂-Lava) zero (x ∷ y ∷ []) 


