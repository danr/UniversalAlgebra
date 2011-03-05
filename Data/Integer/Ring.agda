--------------------------------------------------------------------------------
--
-- Work in progress: (ℤ , _+_ , _*_) forms a commutative ring 
--
-- Code needs to be a litte bit more tidy
--
--------------------------------------------------------------------------------
module Data.Integer.Ring where

open import Data.Integer renaming (suc to ℤsuc ; pred to ℤpred ; ∣_∣ to [_])
open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Product
open import Data.Sign renaming (_*_ to _*S_ ; + to S+ ; - to S-)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Algebra
open import Algebra.Structures
open import Function

open import Data.Integer.Ring.Lemmas 
open import Data.Integer.Ring.Addition
open import Data.Integer.Ring.Multiplication
open import Data.Integer.Ring.Distributivity

import Algebra.FunctionProperties as FP ; open FP {A = ℤ} _≡_

private
  module N where
    open import Data.Nat.Properties
    open CommutativeSemiring commutativeSemiring public

  +-identity : Identity (+ 0) _+_
  +-identity = 0+n≡n , n+0≡n
    where
      0+n≡n : LeftIdentity (+ 0) _+_
      0+n≡n -[1+ n ] = refl
      0+n≡n (+ n) = refl

      n+0≡n : RightIdentity (+ 0) _+_
      n+0≡n -[1+ n ] = refl
      n+0≡n (+ n) = cong +_ (N.+-comm n 0)

  -++ : ∀ m n → - + n + + m ≡ m ⊖ n
  -++ m zero    = refl
  -++ m (suc n) = refl

  +-inverse : Inverse (+ 0) -_ _+_
  +-inverse = left , right
    where
      left : LeftInverse (+ 0) -_ _+_
      left -[1+ zero ] = refl
      left -[1+ suc n ] rewrite left -[1+ n ] = refl
      left (+ zero) = refl
      left (+ suc n) = trans (sym (-++ n n)) (left (+ n))

      right : RightInverse (+ 0) -_ _+_
      right n = trans (+-comm n (- n)) (left n)

  *-identity : Identity (+ 1) _*_
  *-identity = 1*n≡n , n*1≡n
    where
      1*n≡n : LeftIdentity (+ 1) _*_
      1*n≡n -[1+ n ] = cong -[1+_] (N.+-comm n 0)
      1*n≡n (+ zero) = refl
      1*n≡n (+ suc n) = cong (+_ ∘ suc) (N.+-comm n 0)

      n*1≡n : RightIdentity (+ 1) _*_
      n*1≡n -[1+ n ] = cong -[1+_] (trans (N.*-comm n 1) (N.+-comm n 0))
      n*1≡n (+ zero) = refl
      n*1≡n (+ suc n) = cong (+_ ∘ suc) (trans (N.*-comm n 1) (N.+-comm n 0))

isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
isCommutativeRing = record
  { isRing = record 
    { +-isAbelianGroup = record 
      { isGroup = record 
        { isMonoid = record 
          { isSemigroup = record 
            { isEquivalence = isEquivalence
            ; assoc = +-assoc
            ; ∙-cong = cong₂ _+_ 
            }
          ; identity = +-identity 
          }
        ; inverse = +-inverse
        ; ⁻¹-cong = cong -_ 
        }
      ; comm = +-comm 
      }
    ; *-isMonoid = record 
      { isSemigroup = record 
        { isEquivalence = isEquivalence
        ; assoc = *-assoc
        ; ∙-cong = cong₂ _*_ 
        }
      ; identity = *-identity 
      }
    ; distrib = distrib
    }
  ; *-comm = *-comm
  }



