module Preimage where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Equalizer

-- A subset is simply a monic. 

infix 5 _⊆_

data _⊆_ (A B : Set) : Set₁ where
  sub : (f : A → B) (m : Monic f) → A ⊆ B 

[_] : {A B : Set} → A ⊆ B → A → B
[ sub f m ] = f

⟦_⟧  : {A B : Set} (⊆ : A ⊆ B) → Monic [ ⊆ ]
⟦ sub f m ⟧ = m

module Preimage {A B V : Set} (f : A → B) (i : V ⊆ B) where

  --
  --            f̂ 
  -- U=f⁻¹(V) -------> V
  --     |             |
  --     |             |
  --   j |             | i
  --     |             |
  --     ↓             ↓
  --     A ----------> B
  --            f
  --

  data U : Set where
    pre : (a : A) (v : V) (eq : f a ≡ [ i ] v) → U

  infix 10 _⁻¹_ 
  _⁻¹_ = U

  j : U → A 
  j (pre a v eq) = a

  f̂ : U → V
  f̂ (pre a v eq) = v

  commute : f ∘ j ≗ [ i ] ∘ f̂
  commute (pre a v eq) = eq

  j-monic : Monic j
  j-monic = I→M j lemma
    where
      lemma : (x y : U) → j x ≡ j y → x ≡ y
      lemma (pre a v eq) (pre a' v' eq') aeq with veq 
        where
          ivs : [ i ] v ≡ [ i ] v'
          ivs = trans (sym eq) (trans (cong f aeq) eq')
  
          veq : v ≡ v'
          veq = ⟦ i ⟧ (const v) (const v') (const ivs) v
      lemma (pre a v eq) (pre .a .v eq') refl | refl = 
        subst (λ p → pre a v eq ≡ pre a v p) (proof-irrelevance eq eq') refl
