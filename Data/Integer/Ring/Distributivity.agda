module Data.Integer.Ring.Distributivity where

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
--open import Data.Integer.Properties

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

  ◃+ : ∀ s p q → s ◃ (p +ℕ q) ≡ (s ◃ p) + (s ◃ q)
  ◃+ S- zero zero = refl
  ◃+ S- zero (suc p) = refl
  ◃+ S- (suc p) zero = cong -[1+_] (p +0≡0)
  ◃+ S- (suc p) (suc q) = cong -[1+_] (move-suc p q)
  ◃+ S+ zero q = sym (+0+ S+ ◃ q ≡0)
  ◃+ S+ (suc p) zero = refl
  ◃+ S+ (suc p) (suc q) = refl


  distrib++ : ∀ n p q → (+ n) * (+ p + + q) ≡ (+ n) * (+ p) + (+ n) * (+ q)
  distrib++ n p q = cong (_◃_ S+) (proj₁ N.distrib n p q) ~ ◃+ S+ (n *ℕ p) (n *ℕ q)

  distrib-+ : ∀ n p q → (+ suc n) * ((S- ◃ suc p) + (+ q)) ≡ (+ suc n) * (S- ◃ suc p) + (+ suc n) * (+ q)
  distrib-+ n p zero = sym (cong (_+_ -[1+ p +ℕ n *ℕ suc p ]) (zero-lemma S+ n)) 
  distrib-+ n zero (suc p) = +-lemma (p +ℕ n *ℕ p) 
                           ~ cong (_+_ (+ p)) (lemma₀ n p) 
                           ~ lemma⁰ p (n *ℕ suc p) n  
                           ~ cong (λ nr → p +ℕ n *ℕ suc p ⊖ nr) (N.+-comm 0 n ~ N.*-comm 1 n) 
    where
      +-lemma : ∀ n → S+ ◃ n ≡ + n
      +-lemma zero = refl
      +-lemma (suc n) = refl

      lemma″ : ∀ m n → (+ 1) + (m ⊖ n) ≡ suc m ⊖ n
      lemma″ m zero = refl
      lemma″ zero (suc n) = refl
      lemma″ (suc m) (suc n) = lemma″ m n
  
      lemma⁰ : ∀ m n k → (+ m) + (n ⊖ k) ≡ (m +ℕ n) ⊖ k
      lemma⁰ zero    n k = +0+ n ⊖ k ≡0
      lemma⁰ (suc m) n k = +-assoc (+ 1) (+ m) (n ⊖ k) 
                         ~ cong ℤsuc (lemma⁰ m n k) 
                         ~ lemma″ (m +ℕ n) k
  
      lemma₀ : ∀ m n → + (m *ℕ n) ≡ m *ℕ suc n ⊖ m 
      lemma₀ zero n = refl
      lemma₀ (suc m) n = cong (_+_ (+ n)) (lemma₀ m n) ~ lemma⁰ n (m *ℕ suc n) m

  distrib-+ n (suc p) (suc q) = distrib-+ n p q ~ lemma (p +ℕ n *ℕ suc p) (suc n *ℕ q) 
                              ~ lemma′ n (q +ℕ n *ℕ q) (suc (p +ℕ n *ℕ suc p)) 
                              ~ cong₂ _⊖_
                                  (sym (N.+-assoc n q (n *ℕ q)) 
                                    ~ (cong (λ r → r +ℕ (n *ℕ q)) (N.+-comm n q)) 
                                    ~ N.+-assoc q n (n *ℕ q) 
                                    ~ cong (_+ℕ_ q) (gluppe n q))  
                                  (move-suc n (p +ℕ n *ℕ suc p) 
                                    ~ cong suc (sym (N.+-assoc n p (n *ℕ suc p))) 
                                    ~ cong (λ r → suc (r +ℕ n *ℕ suc p)) (N.+-comm n p) 
                                    ~ cong suc (N.+-assoc p n (n *ℕ suc p)) 
                                    ~ cong (suc ∘ _+ℕ_ p) (gluppe n (suc p)))


    where
      gluppe : ∀ n p → n +ℕ n *ℕ p ≡ n *ℕ suc p
      gluppe n p = cong (_+ℕ_ n) (N.*-comm n p) ~ sym (N.*-comm n (suc p))

      lemma : ∀ x y → -[1+ x ] + (S+ ◃ y) ≡ y ⊖ suc x
      lemma x zero    = refl
      lemma x (suc n) = refl
  
      lemma₂ : ∀ x y → x ⊖ y ≡ suc x ⊖ suc y
      lemma₂ x y = refl

      lemma′ : ∀ k x y → x ⊖ y ≡ (k +ℕ x) ⊖ (k +ℕ y)
      lemma′ zero x y = refl
      lemma′ (suc k) x y = lemma′ k x y
                

  distrib+- : ∀ n p q → (+ suc n) * ((+ p) + (S- ◃ suc q)) ≡ (+ suc n) * (+ p) + (+ suc n) * (S- ◃ suc q)
  distrib+- n p q = begin
      (+ suc n) * (+ p + (S- ◃ suc q))             ≡⟨ distrib-+ n q p ⟩  
      (+ suc n) * (S- ◃ suc q) + (+ suc n) * (+ p) ≡⟨ +-comm ((+ suc n) * (S- ◃ suc q)) ((+ suc n) * (+ p)) ⟩  
      (+ suc n) * + p + (+ suc n) * (S- ◃ suc q)
    ∎ where open ≡-Reasoning

  distrib- : ∀ n p q → (+ n) * (-[1+ p ] + -[1+ q ]) ≡ (+ n) * -[1+ p ] + (+ n) * -[1+ q ]
  distrib- n p q = cong (_◃_ S-) lemma ~ ◃+ S- (n *ℕ suc p) (n *ℕ suc q)
    where 
      lemma = begin
        n *ℕ suc (suc (p +ℕ q))  ≡⟨ cong (_*ℕ_ n ∘ suc) (sym (move-suc p q)) ⟩
        n *ℕ suc (p +ℕ suc q)    ≡⟨ proj₁ N.distrib n (suc p) (suc q) ⟩
        n *ℕ suc p +ℕ n *ℕ suc q
       ∎ where open ≡-Reasoning        

  negate-lem₀ : ∀ x y → - (x ⊖ y) ≡ y ⊖ x
  negate-lem₀ zero zero = refl
  negate-lem₀ zero (suc y) = refl
  negate-lem₀ (suc x) zero = refl
  negate-lem₀ (suc x) (suc y) = negate-lem₀ x y

  negate-lem₁ : ∀ s x → opposite s ◃ x ≡ - (s ◃ x)
  negate-lem₁ S- zero = refl
  negate-lem₁ S- (suc n) = refl
  negate-lem₁ S+ zero = refl
  negate-lem₁ S+ (suc n) = refl

  negate-lem₂ : ∀ s t x y → - ((s ◃ x) + (t ◃ y)) ≡ (opposite s ◃ x) + (opposite t ◃ y)
  negate-lem₂ s  t  zero zero = refl
  negate-lem₂ S- S- zero (suc y) = refl
  negate-lem₂ S- S- (suc x) zero = cong (+_ ∘ suc) (N.+-comm 0 x)
  negate-lem₂ S- S- (suc x) (suc y) = cong (+_ ∘ suc) (sym (move-suc x y))
  negate-lem₂ S+ S- zero (suc y) = refl
  negate-lem₂ S+ S- (suc x) zero = cong -[1+_] (N.+-comm x 0)
  negate-lem₂ S+ S- (suc x) (suc y) = negate-lem₀ x y
  negate-lem₂ S- S+ zero (suc y) = refl
  negate-lem₂ S- S+ (suc x) zero = cong (+_ ∘ suc) (N.+-comm 0 x)
  negate-lem₂ S- S+ (suc x) (suc y) = negate-lem₀ y x
  negate-lem₂ S+ S+ zero (suc y) = refl
  negate-lem₂ S+ S+ (suc x) zero = cong -[1+_] (N.+-comm x 0)
  negate-lem₂ S+ S+ (suc x) (suc y) = cong -[1+_] (move-suc x y)

  negate-distrib : ∀ x p q 
                 → (+ suc x) * (p + q) ≡ (+ suc x) * p + (+ suc x) * q
                 → -[1+ x ] * (p + q) ≡ -[1+ x ] * p + -[1+ x ] * q
  negate-distrib x p q eq = 
              negate-lem₁ (sign (p + q)) ([ p + q ] +ℕ x *ℕ [ p + q ]) 
            ~ cong -_ eq
            ~ negate-lem₂ (sign p) (sign q) ([ p ] +ℕ x *ℕ [ p ]) ([ q ] +ℕ x *ℕ [ q ])

  distribˡ : _*_ DistributesOverˡ _+_ -- ∀ x y z → x * (y + z) ≡ x * y + x * z
  distribˡ (+ zero) y z = refl
  distribˡ (+ suc x) -[1+ p ] -[1+ q ] = distrib-  (suc x) p q
  distribˡ (+ suc x) -[1+ p ]   (+ q)  = distrib-+ x       p q
  distribˡ (+ suc x) (+ p)    -[1+ q ] = distrib+- x       p q
  distribˡ (+ suc x) (+ p)      (+ q)  = distrib++ (suc x) p q
  distribˡ -[1+ x ]  -[1+ p ] -[1+ q ] = negate-distrib x -[1+ p ] -[1+ q ] (distrib-  (suc x) p q )
  distribˡ -[1+ x ]  -[1+ p ]   (+ q)  = negate-distrib x -[1+ p ]   (+ q)  (distrib-+      x  p q )
  distribˡ -[1+ x ]  (+ p)    -[1+ q ] = negate-distrib x (+ p)    -[1+ q ] (distrib+-      x  p q )
  distribˡ -[1+ x ]  (+ p)      (+ q)  = negate-distrib x (+ p)      (+ q)  (distrib++ (suc x) p q )

distrib : _*_ DistributesOver _+_
distrib = distribˡ , λ x y z → *-comm (y + z) x 
                             ~ distribˡ x y z 
                             ~ cong₂ _+_ (*-comm x y) (*-comm x z) 
