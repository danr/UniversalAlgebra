--
--
-- Parallell vectors for one sole purpose,
-- making a vector of a function
--
--  {n} {B : Fin n → Set} → (Fin n) → B x
--
-- And needs a major tidy up (obviously)
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

data ParVec {i} {j} {A : Set i} (B : A → Set j) : {n : ℕ} → Vec A n → Set ((i ⊔ j)) where
  []  : ParVec B []
  _∷_ : ∀ {n x} {xs : Vec A n} (p : B x) (ps : ParVec B xs) → ParVec B (x ∷ xs)

mapOverlay : ∀ {n : ℕ} {i} {j} {k} {A : Set i} {B : A → Set j} {C : A → Set k} 
           → {xs : Vec A n} → (∀ {a} → B a → C a) → ParVec B xs → ParVec C xs
mapOverlay f []       = []
mapOverlay f (x ∷ xs) = f x ∷ mapOverlay f xs 

-- A little more convenient to use than allFin
count : (n : ℕ) → Vec (Fin n) n
count zero    = []
count (suc n) = zero ∷ map suc (count n)

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

par-lookup : ∀ {n : ℕ} {i} {j} {A : Set i} {B : A → Set j} 
            → {xs : Vec A n} → ParVec B xs → (x : Fin n) → B (lookup x xs)
par-lookup []       ()
par-lookup (p ∷ ps) zero    = p
par-lookup (p ∷ ps) (suc i) = par-lookup ps i 

uncount : ∀ {n : ℕ} {i} {B : Fin n → Set i} → ParVec B (count n) → (x : Fin n) → B x
uncount {n} {i} {B} xs x = subst B (count-lookup n x) (par-lookup xs x) 

-- Some silly examples
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

  function : (x : Fin 3) → ⟦ lookup x types ⟧
  function = uncount (3 ∷ false ∷ 8 ∷ [])


