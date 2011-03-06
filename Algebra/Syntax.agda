------------------------------------------------
--
-- A little practice with anonymous identifiers
--
-- Todo: tidy up
--

{-# OPTIONS --universe-polymorphism #-}
module Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.List
open import Data.Vec.N-ary

Env : (k n : ℕ) → Set
Env k n = Vec (Fin k) n

run′ : (k n : ℕ) → N-ary n (Fin k) Set
run′ k zero    = List (Fin k)
run′ k (suc n) = λ i → run′ k n

run″ : (k n : ℕ) → Env k n → ∀ⁿ n (run′ k n) → List (Fin k)
run″ k zero    Γ        = λ xs → xs 
run″ k (suc n) (x ∷ xs) = λ f → run″ k n xs (f x)
  
run : (n : ℕ) → ∀ⁿ n (run′ n n) → List (Fin n)
run n = run″ n n (allFin n)

blooper : List (Fin 3)
blooper = run 3 (λ x y z → x ∷ y ∷ z ∷ x ∷ y ∷ [])   -- x is fin 0, y is fin 1, z in fin 2
