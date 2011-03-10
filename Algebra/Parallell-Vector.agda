--
--
-- Parallell vectors for one sole purpose,
-- making a vector of a function
--
--  {n} {B : Fin n → Set} → (Fin n) → B x
--
-- Should not be in Algebra,
--
-- And needs a major tidy up (obviously)
--

{-# OPTIONS --universe-polymorphism #-}
module Algebra.Parallell-Vector where

open import Data.Fin renaming (_+_ to _+Fin_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_⊔_ ; pred)
open import Data.Vec renaming (map to map′)
open import Level

infixr 5 _∷_

data ParVec {i} {j} {A : Set i} (B : A → Set j) : {n : ℕ} → Vec A n → Set (suc (i ⊔ j)) where
  []  : ParVec B []
  _∷_ : ∀ {n x′} {xs′ : Vec A n} (x : B x′) (xs : ParVec B xs′) → ParVec B (x′ ∷ xs′)

map : ∀ {n : ℕ} {i} {j} {k} {A : Set i} {B : A → Set j} {C : A → Set k} 
        {xs : Vec A n} → (∀ {a} → B a → C a) → ParVec B xs → ParVec C xs
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs 


module Example where

  open import Data.Fin
  open import Data.Bool

  data Type : Set where
    TNat TBool : Type

  ⟦_⟧ : Type → Set
  ⟦ TNat  ⟧ = ℕ
  ⟦ TBool ⟧ = Bool

  types : Vec Type 3
  types = TNat ∷ TBool ∷ TNat ∷ []

  values : ParVec ⟦_⟧ types 
  values = 4 ∷ true ∷ 9 ∷ []

  test : ParVec (λ x → ⟦ lookup x types ⟧) (allFin 3)
  test = 10 ∷ false ∷ 2 ∷ []

-- A little more convenient to use than allFin
count : (n : ℕ) → Vec (Fin n) n
count zero = []
count (suc n) = zero ∷ map′ suc (count n)

-- Maybe too general with m
up : {m : ℕ} (n : ℕ) (p : Fin n) (xs : Vec (Fin m) n) → _≡_ {A = Fin (suc m)} (lookup p (map′ suc xs)) (suc (lookup p xs)) 
up .(suc n) (zero {n}) (x ∷ xs) = refl
up .(suc n) (suc {n} i) (x ∷ xs) = up n i  xs

lc : (n : ℕ) (p : Fin n) → lookup p (count n) ≡ p
lc .(suc n) (zero {n}) = refl
lc .(suc n) (suc {n} i) = trans (up n i (count n)) (cong suc (lc n i))

parlook : ∀ {n : ℕ} {i} {j} {A : Set i} {B : A → Set j} 
        → (xs : Vec A n) → ParVec B xs → (x : Fin n) → B (lookup x xs)
parlook []       []       ()
parlook (x ∷ xs) (p ∷ ps) zero = p
parlook (x ∷ xs) (p ∷ ps) (suc i) = parlook xs ps i 

-- subst for the rescue!!
unpar : ∀ {n : ℕ} {i} {B : Fin n → Set i} → ParVec B (count n) → (x : Fin n) → B x
unpar {n} {i} {B} xs x = subst B (lc n x) (parlook (count n) xs x) 



