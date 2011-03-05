module Data.Integer.Ring.Addition where

-- Associativity for integers
-- It's quite tricky to find out names for all the lemmas, please bear with me!
-- The lemmas for the eight combinations of the signs of the integers in the
-- associativity are simply named lem#.

open import Data.Integer renaming (suc to ℤsuc ; pred to ℤpred)
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Algebra
open import Algebra.Structures
open import Function

open import Data.Integer.Ring.Lemmas

import Algebra.FunctionProperties as FP ; open FP {A = ℤ} _≡_

private 
  module N where
    open import Data.Nat.Properties
    open CommutativeSemiring commutativeSemiring public

+-comm : Commutative _+_
+-comm -[1+ p ] -[1+ q ] = cong (λ x → -[1+ suc x ]) (N.+-comm p q)
+-comm -[1+ p ] (+ q) = refl
+-comm (+ p) -[1+ q ] = refl
+-comm (+ p) (+ q) = cong +_ (N.+-comm p q)

private

  move-plus : ∀ p q → suc p ⊖ q ≡ + 1 + (p ⊖ q)
  move-plus p zero = refl
  move-plus zero (suc n) = refl
  move-plus (suc n) (suc n') = move-plus n n'
   
  move-minus : ∀ p q → p ⊖ suc q ≡ p ⊖ q - + 1
  move-minus p zero = refl
  move-minus zero (suc n) = refl
  move-minus (suc n) (suc n') = move-minus n n'
   
  move-minus' : ∀ p q → p ⊖ suc q ≡ -[1+ 0 ] + (p ⊖ q)
  move-minus' zero zero = refl
  move-minus' zero (suc n) = refl
  move-minus' (suc n) zero = refl
  move-minus' (suc n) (suc n') = move-minus' n n'
   
  decr : ∀ p q r → p ⊖ q ≡ -[1+ r ] → p ⊖ suc q ≡ -[1+ suc r ]
  decr p q r eq = trans (move-minus p q) (cong ℤpred eq)
   
  incr : ∀ a b c → a ⊖ suc b ≡ + c → a ⊖ b ≡ + suc c
  incr zero b c eq = cong ℤsuc eq
  incr (suc a) b c eq = incr' a b c eq
    where
      incr' : ∀ p q r → p ⊖ q ≡ + r → suc p ⊖ q ≡ + suc r
      incr' p q r eq = trans (move-plus p q) (cong ℤsuc eq)
   
  left-addsuc : ∀ a b c d → a ⊖ b ≡ c ⊖ d → a ⊖ suc b ≡ c ⊖ suc d
  left-addsuc a b c d eq = trans (move-minus a b) (trans (cong (λ x → x - + 1) eq) (sym (move-minus c d)))
   
  left-remsuc : ∀ a b c d → a ⊖ suc b ≡ c ⊖ suc d → a ⊖ b ≡ c ⊖ d
  left-remsuc zero b zero d eq = cong ℤsuc eq
  left-remsuc zero b (suc c) d eq = trans (cong ℤsuc eq) (sym (move-plus c d))
  left-remsuc (suc a) b zero d eq = trans (move-plus a b) (cong ℤsuc eq)
  left-remsuc (suc a) b (suc c) d eq = trans (move-plus a b) (trans (cong ℤsuc eq) (sym (move-plus c d)))
   
  lemma-pred : ∀ a b c d → -[1+ a ] + b ≡ -[1+ c ] + d → -[1+ suc a ] + b ≡ -[1+ suc c ] + d 
  lemma-pred a -[1+ b ] c -[1+ d ] eq = cong ℤpred eq
  lemma-pred a -[1+ b ] c (+ d) eq = sym (decr d (suc c) (suc (a +ℕ b)) (sym eq)) 
  lemma-pred a (+ b) c -[1+ d ] eq =      decr b (suc a) (suc (c +ℕ d)) eq 
  lemma-pred a (+ b) c (+ d) eq = left-addsuc b (suc a) d (suc c) eq
   
  lemma-suc : ∀ a b c d → + a + b ≡ + c + d → + suc a + b ≡ + suc c + d 
  lemma-suc a -[1+ b ] c -[1+ d ] eq = left-remsuc a b c d eq
  lemma-suc a -[1+ b ] c (+ d) eq =      incr a b (c +ℕ d) eq
  lemma-suc a (+ b) c -[1+ d ] eq = sym (incr c d (a +ℕ b) (sym eq))
  lemma-suc a (+ b) c (+ d) eq = cong ℤsuc eq 
   
  lem₁ : ∀ p q r → r ⊖ suc (p +ℕ q) ≡ -[1+ p ] + (r ⊖ q)
  lem₁ p zero r = cong (λ n → r ⊖ suc n) (p +0≡0)
  lem₁ p (suc q) zero = cong -[1+_] (move-suc p q)
  lem₁ p (suc q) (suc r) = trans (cong (_⊖_ r) (move-suc p q)) (lem₁ p q r)
   
  lem₂ : ∀ p q r → q ⊖ suc p + -[1+ r ] ≡ -[1+ p ] + (q ⊖ suc r)
  lem₂ p zero r = refl
  lem₂ zero (suc q) r = move-minus' q r
  lem₂ (suc p) (suc q) zero = trans (+-comm (q ⊖ suc p) -[1+ zero ]) (sym (move-minus' q (suc p)))
  lem₂ (suc p) (suc q) (suc r) = trans (+-comm (q ⊖ suc p) -[1+ suc r ]) 
                                       (lemma-pred r (q ⊖ suc p) p (q ⊖ suc r) 
                                                   (trans (+-comm -[1+ r ] (q ⊖ suc p)) 
                                                          (lem₂ p q r))) 
   
  lem₃ : ∀ p q r → q ⊖ p + + r ≡ q +ℕ r ⊖ p
  lem₃ zero q r = refl
  lem₃ (suc p) zero r = refl
  lem₃ (suc p) (suc q) r = lem₃ p q r
   
  lem₄ : ∀ p q r → p ⊖ q + -[1+ r ] ≡ p ⊖ suc (q +ℕ r)
  lem₄ p q r = trans (lem₂ q (suc p) r) (sym (lem₁ q r p))
   
  lem₅ : ∀ p q r → p ⊖ q + + r ≡ + p + (r ⊖ q)
  lem₅ zero zero r = refl
  lem₅ zero (suc p) r = sym +0+ r ⊖ suc p ≡0 
  lem₅ (suc p) zero r = refl
  lem₅ (suc p) (suc q) zero = trans (+-comm (p ⊖ q) (+ 0)) (+0+ p ⊖ q ≡0)
  lem₅ (suc p) (suc q) (suc r) = trans (+-comm (p ⊖ q) (+ suc r)) 
                                       (lemma-suc r (p ⊖ q) p (r ⊖ q) 
                                                  (trans (+-comm (+ r) (p ⊖ q)) 
                                                         (lem₅ p q r)))
   
  lem₆ : ∀ p q r → p +ℕ q ⊖ suc r ≡ + p + (q ⊖ suc r)
  lem₆ p q r = trans (sym (lem₃ (suc r) p q)) (lem₅ p (suc r) q) 

+-assoc : Associative _+_
+-assoc -[1+ p ] -[1+ q ] -[1+ r ] = cong (λ n → -[1+ suc n ]) 
                                          (trans (cong suc (N.+-assoc p q r)) 
                                                 (sym (move-suc p (q +ℕ r))))
+-assoc -[1+ p ] -[1+ q ]   (+ r)  = trans (cong (λ n → r ⊖ (suc n)) (sym (move-suc p q))) 
                                           (lem₁ p (suc q) r)
+-assoc -[1+ p ]   (+ q)  -[1+ r ] = lem₂ p q r 
+-assoc -[1+ p ]   (+ q)    (+ r)  = lem₃ (suc p) q r
+-assoc   (+ p)  -[1+ q ] -[1+ r ] = lem₄ p (suc q) r
+-assoc   (+ p)  -[1+ q ]   (+ r)  = lem₅ p (suc q) r
+-assoc   (+ p)    (+ q)  -[1+ r ] = lem₆ p q r
+-assoc   (+ p)    (+ q)    (+ r)  = cong +_ (N.+-assoc p q r)

