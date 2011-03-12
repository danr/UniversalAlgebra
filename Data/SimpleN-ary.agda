{-# OPTIONS --universe-polymorphism #-}
module Data.SimpleN-ary where

open import Data.Nat
open import Data.Vec
 
Op : ∀ {i} → ℕ → Set i → Set i 
Op zero    A = A
Op (suc n) A = A → Op n A 

apply : ∀ {i} {X : Set i} (n : ℕ) → Op n X → Vec X n → X
apply zero    f []       = f
apply (suc n) f (x ∷ xs) = apply n (f x) xs

makeOp : ∀ {i} {X : Set i} (n : ℕ) → (Vec X n → X) → Op n X
makeOp zero    f = f []
makeOp (suc n) f = λ x → makeOp n (λ xs → f (x ∷ xs))

Relf : ∀ {i} → ℕ → Set → Set i → Set i
Relf zero    A B = B
Relf (suc n) A B = A → Relf n A B
