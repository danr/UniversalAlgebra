module Data.Sign.Props where

open import Data.Sign
open import Data.Product

open import Level

open import Algebra
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality

import Algebra.FunctionProperties as FP ; open FP {A = Sign} _≡_

private

  comm : Commutative _*_ 
  comm - - = refl
  comm - + = refl
  comm + - = refl
  comm + + = refl

  assoc : Associative _*_
  assoc - - - = refl
  assoc - - + = refl
  assoc - + t = refl
  assoc + s t = refl


commutativeMonoid : CommutativeMonoid zero zero
commutativeMonoid = record 
  { Carrier = Sign
  ; _≈_ = _≡_
  ; _∙_ = _*_
  ; ε = +
  ; isCommutativeMonoid = record 
    { isSemigroup = record 
      { isEquivalence = isEquivalence
      ; assoc = assoc
      ; ∙-cong = cong₂ _*_ 
      }
    ; identityˡ = λ x → refl
    ; comm = comm 
    }
  }

  

