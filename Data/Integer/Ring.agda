--------------------------------------------------------------------------------
--
-- Work in progress: (ℤ , _+_ , _*_) forms a commutative ring 
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

open import Data.Integer.Lemmas using (+-comm ; +-assoc ; _+0≡0 ; move-suc)

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
      left (+ suc n) = trans (sym $ -++ n n) (left (+ n))

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

  S*comm : ∀ s r → s *S r ≡ r *S s
  S*comm S- S- = refl
  S*comm S- S+ = refl
  S*comm S+ S- = refl
  S*comm S+ S+ = refl

  *-comm : Commutative _*_
  *-comm x y = cong₂ _◃_ (S*comm (sign x) (sign y)) (N.*-comm [ x ] [ y ])

  open import Data.Integer.Properties

  infixr 1 _~_

  _~_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ~ q = trans p q

  zero-elim : ∀ n → n *ℕ 0 ≡ 0
  zero-elim n = N.*-comm n 0

  sign-assoc : ∀ s t u → (s *S t) *S u ≡ s *S (t *S u)
  sign-assoc S- S- S- = refl
  sign-assoc S- S- S+ = refl
  sign-assoc S- S+ u = refl
  sign-assoc S+ t u = refl

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

  zero-lemma : ∀ s n → s ◃ n *ℕ 0 ≡ + 0
  zero-lemma s zero = refl
  zero-lemma s (suc n) = zero-lemma s n

  ◃-zero : ∀ s {n} → n ≡ 0 → s ◃ n ≡ + 0
  ◃-zero s = cong (_◃_ s)

  sign-irrelevance-zero : ∀ {s t n m} → n ≡ 0 → m ≡ 0 → s ◃ n ≡ t ◃ m
  sign-irrelevance-zero refl refl = refl

  sign-lemma : ∀ s t u p q → sign (s ◃ [ t ◃ suc p ] *ℕ [ u ◃ suc q ]) ≡ s 
  sign-lemma s t u p q = cong (sign ∘ (_◃_ s)) (mul-lemma t u p q) 
                       ~ cong sign (helper s (t *S u) (q +ℕ p *ℕ suc q))
                       ~ sign-◃ s (q +ℕ p *ℕ suc q)
  


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

           ≡⟨ sign-assoc (sign (s ◃ suc p)) (sign (t ◃ suc q)) (sign (u ◃ suc r)) ⟩

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


  +0+_≡0 : ∀ n → + 0 + n ≡ n 
  +0+ -[1+ n ] ≡0 = refl
  +0+ + n      ≡0 = refl

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

  gluppe : ∀ n p → n +ℕ n *ℕ p ≡ n *ℕ suc p
  gluppe n p = cong (_+ℕ_ n) (N.*-comm n p) ~ sym (N.*-comm n (suc p))

  distrib-+ : ∀ n p q → (+ suc n) * ((S- ◃ suc p) + (+ q)) ≡ (+ suc n) * (S- ◃ suc p) + (+ suc n) * (+ q)
  distrib-+ n zero zero = {!!}
  distrib-+ n zero (suc p) = {!!}
  distrib-+ n (suc p) zero = {!!}
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
      lemma : ∀ x y → -[1+ x ] + (S+ ◃ y) ≡ y ⊖ suc x
      lemma x y = {!!}
  
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

  distrib : ∀ x y z → x * (y + z) ≡ x * y + x * z
  distrib (+ zero) y z = refl
  distrib (+ suc x) -[1+ p ] -[1+ q ] = distrib-  (suc x) p q
  distrib (+ suc x) -[1+ p ]   (+ q)  = distrib-+ x       p q
  distrib (+ suc x) (+ p)    -[1+ q ] = distrib+- x       p q
  distrib (+ suc x) (+ p)      (+ q)  = distrib++ (suc x) p q
  distrib -[1+ x ]  -[1+ p ] -[1+ q ] = negate-distrib x -[1+ p ] -[1+ q ] (distrib-  (suc x) p q )
  distrib -[1+ x ]  -[1+ p ]   (+ q)  = negate-distrib x -[1+ p ]   (+ q)  (distrib-+      x  p q )
  distrib -[1+ x ]  (+ p)    -[1+ q ] = negate-distrib x (+ p)    -[1+ q ] (distrib+-      x  p q )
  distrib -[1+ x ]  (+ p)      (+ q)  = negate-distrib x (+ p)      (+ q)  (distrib++ (suc x) p q )

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
    ; distrib = distrib , {!!} 
    }
  ; *-comm = *-comm
  }



