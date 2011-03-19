--
-- Parallell vectors, can for instance be used to go between a 
-- vector and a function of type
--
--  {n : ℕ} {B : Fin n → Set} → (Fin n) → B x
--
-- (see uncount)
--

{-# OPTIONS --universe-polymorphism #-}
module Data.ParallelVector where

open import Data.Fin
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality
open import Level

infixr 5 _∷_

data ParVec {i} {j} {A : Set i} (B : A → Set j) : {n : ℕ} → Vec A n → Set (i ⊔ j) where
  []  : ParVec B []
  _∷_ : ∀ {n x} {xs : Vec A n} (p : B x) (ps : ParVec B xs) → ParVec B (x ∷ xs)

par-lookup : ∀ {n : ℕ} {i} {j} {A : Set i} {B : A → Set j} 
            → {xs : Vec A n} → ParVec B xs → (x : Fin n) → B (lookup x xs)
par-lookup []       ()
par-lookup (p ∷ ps) zero    = p
par-lookup (p ∷ ps) (suc i) = par-lookup ps i 

-- A little more convenient to use here than allFin
-- All numbers from 0 .. n-1
count : (n : ℕ) → Vec (Fin n) n
count zero    = []
count (suc n) = zero ∷ map suc (count n)

-- Lemmas to the uncount function
private
  suc-lookup : {m : ℕ} (n : ℕ) (i : Fin n) (xs : Vec (Fin m) n) 
             → _≡_ {A = Fin (suc m)} (lookup i (map suc xs)) (suc (lookup i xs)) 
  suc-lookup zero    ()      []
  suc-lookup (suc n) zero    (x ∷ xs) = refl
  suc-lookup (suc n) (suc i) (x ∷ xs) = suc-lookup n i xs
  
  count-lookup : (n : ℕ) (p : Fin n) → lookup p (count n) ≡ p
  count-lookup zero    ()
  count-lookup (suc n) zero    = refl
  count-lookup (suc n) (suc i) = trans (suc-lookup n i (count n)) 
                                       (cong suc (count-lookup n i))
  
uncount : ∀ {n : ℕ} {i} {B : Fin n → Set i} → ParVec B (count n) → (x : Fin n) → B x
uncount {n} {i} {B} xs x = subst B (count-lookup n x) (par-lookup xs x) 

-- Some silly examples
private 

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

  function : (x : Fin 3) → ⟦ lookup x types ⟧
  function = uncount (3 ∷ false ∷ 8 ∷ [])


