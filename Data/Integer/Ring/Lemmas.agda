module Data.Integer.Ring.Lemmas where
 
open import Data.Integer renaming (suc to ℤsuc ; pred to ℤpred)
open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Algebra
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private 
  module N where
    open import Data.Nat.Properties
    open CommutativeSemiring commutativeSemiring public

move-suc : ∀ p q → p +ℕ suc q ≡ suc (p +ℕ q)
move-suc p q = trans (N.+-comm p (suc q)) (cong suc (N.+-comm q p))

_+0≡0 : ∀ n → n +ℕ 0 ≡ n
zero +0≡0 = refl
suc n +0≡0 = cong suc (n +0≡0)

+0+_≡0 : ∀ n → + 0 + n ≡ n 
+0+ -[1+ n ] ≡0 = refl
+0+ + n      ≡0 = refl

zero-lemma : ∀ s n → s ◃ n *ℕ 0 ≡ + 0
zero-lemma s zero = refl
zero-lemma s (suc n) = zero-lemma s n

