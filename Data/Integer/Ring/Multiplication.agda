module Data.Integer.Ring.Multiplication where

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
open import Data.Integer.Properties

import Algebra.FunctionProperties as FP ; open FP {A = ℤ} _≡_

private
  module N where
    open import Data.Nat.Properties
    open CommutativeSemiring commutativeSemiring public

  module S where
    open import Data.Sign.Props
    open CommutativeMonoid commutativeMonoid public

  infixr 1 _~_

  _~_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ~ q = trans p q

  zero-elim : ∀ n → n *ℕ 0 ≡ 0
  zero-elim n = N.*-comm n 0

  mul-lemma : ∀ s t p q → [ s ◃ suc p ] *ℕ [ t ◃ suc q ] ≡ [ s *S t ◃ suc (q +ℕ p *ℕ suc q) ]
  mul-lemma S- S- p q = refl
  mul-lemma S- S+ p q = refl
  mul-lemma S+ S- p q = refl
  mul-lemma S+ S+ p q = refl

  helper : ∀ s t r → s ◃ [ t ◃ suc r ] ≡ s ◃ suc r
  helper S- S- r = refl
  helper S- S+ r = refl
  helper S+ S- r = refl
  helper S+ S+ r = refl

  ◃-zero : ∀ s {n} → n ≡ 0 → s ◃ n ≡ + 0
  ◃-zero s = cong (_◃_ s)

  sign-irrelevance-zero : ∀ {s t n m} → n ≡ 0 → m ≡ 0 → s ◃ n ≡ t ◃ m
  sign-irrelevance-zero refl refl = refl

  sign-lemma : ∀ s t u p q → sign (s ◃ [ t ◃ suc p ] *ℕ [ u ◃ suc q ]) ≡ s 
  sign-lemma s t u p q = cong (sign ∘ (_◃_ s)) (mul-lemma t u p q) 
                       ~ cong sign (helper s (t *S u) (q +ℕ p *ℕ suc q))
                       ~ sign-◃ s (q +ℕ p *ℕ suc q)

*-comm : Commutative _*_
*-comm x y = cong₂ _◃_ (S.comm (sign x) (sign y)) (N.*-comm [ x ] [ y ])
  
*-assoc : Associative _*_
*-assoc x y z with signAbs x | signAbs y | signAbs z 
*-assoc .(+ 0)   .(t ◃ q) .(u ◃ r) | s ◂ zero | t ◂ q     | u ◂ r    = refl

*-assoc .(s ◃ p) .(+ 0)   .(u ◃ r) | s ◂ p    | t ◂ zero  | u ◂ r    = sign-irrelevance-zero left right 
  where
    left : [ sign (s ◃ p) *S S+ ◃ [ s ◃ p ] *ℕ 0 ] *ℕ [ u ◃ r ] ≡ 0
    left = cong (λ pr → [ pr ] *ℕ [ u ◃ r ])
                (zero-lemma (sign (s ◃ p) *S S+) [ s ◃ p ])

    right : [ s ◃ p ] *ℕ 0 ≡ 0
    right = zero-elim [ s ◃ p ]

*-assoc .(s ◃ p) .(t ◃ q) .(+ 0)   | s ◂ p    | t ◂ q     | u ◂ zero =  sign-irrelevance-zero left right
  where
    left : [ sign (s ◃ p) *S sign (t ◃ q) ◃ [ s ◃ p ] *ℕ [ t ◃ q ] ] *ℕ 0 ≡ 0
    left = zero-elim [ sign (s ◃ p) *S sign (t ◃ q) ◃ [ s ◃ p ] *ℕ [ t ◃ q ] ]

    right : [ s ◃ p ] *ℕ [ sign (t ◃ q) *S S+ ◃ [ t ◃ q ] *ℕ 0 ] ≡ 0
    right = cong (λ pr → [ s ◃ p ] *ℕ [ pr ]) 
                 (zero-lemma (sign (t ◃ q) *S S+) [ t ◃ q ]) 
          ~ zero-elim [ s ◃ p ]

*-assoc .(s ◃ suc p) .(t ◃ suc q) .(u ◃ suc r) | s ◂ suc p | t ◂ suc q | u ◂ suc r = cong₂ _◃_ signs values
  where
    signs = begin
      sign ((sign (s ◃ suc p) *S sign (t ◃ suc q)) ◃ [ s ◃ suc p ] *ℕ [ t ◃ suc q ]) *S sign (u ◃ suc r) 
        
         ≡⟨ cong (λ sr → sr *S sign (u ◃ suc r)) 
                 (sign-lemma (sign (s ◃ suc p) *S sign (t ◃ suc q)) s t p q) ⟩

      (sign (s ◃ suc p) *S sign (t ◃ suc q)) *S sign (u ◃ suc r)

         ≡⟨ S.assoc (sign (s ◃ suc p)) (sign (t ◃ suc q)) (sign (u ◃ suc r)) ⟩

      sign (s ◃ suc p) *S (sign (t ◃ suc q) *S sign (u ◃ suc r))

         ≡⟨ cong (λ sr → sign (s ◃ suc p) *S sr) 
                 (sym (sign-lemma (sign (t ◃ suc q) *S sign (u ◃ suc r)) t u q r )) ⟩

      sign (s ◃ suc p) *S sign (sign (t ◃ suc q) *S sign (u ◃ suc r) ◃ [ t ◃ suc q ] *ℕ [ u ◃ suc r ])

      ∎ 
     where open ≡-Reasoning

    values = begin
      [ sign (s ◃ suc p) *S sign (t ◃ suc q) ◃ [ s ◃ suc p ] *ℕ [ t ◃ suc q ] ] *ℕ [ u ◃ suc r ]

         ≡⟨ cong (λ nr → nr *ℕ [ u ◃ suc r ]) (abs-◃ (sign (s ◃ suc p) *S sign (t ◃ suc q)) 
                                                     ([ s ◃ suc p ] *ℕ [ t ◃ suc q ])) ⟩

      ([ s ◃ suc p ] *ℕ [ t ◃ suc q ]) *ℕ [ u ◃ suc r ]

         ≡⟨ N.*-assoc [ s ◃ suc p ] [ t ◃ suc q ] [ u ◃ suc r ] ⟩

      [ s ◃ suc p ] *ℕ ([ t ◃ suc q ] *ℕ [ u ◃ suc r ])

         ≡⟨ cong (λ nr → [ s ◃ suc p ] *ℕ nr) (sym (abs-◃ (sign (t ◃ suc q) *S sign (u ◃ suc r)) 
                                                   ([ t ◃ suc q ] *ℕ [ u ◃ suc r ]))) ⟩

      [ s ◃ suc p ] *ℕ [ sign (t ◃ suc q) *S sign (u ◃ suc r) ◃ [ t ◃ suc q ] *ℕ [ u ◃ suc r ] ]
     
      ∎ 
     where open ≡-Reasoning


