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
open import Data.List renaming (map to map′)
open import Data.Vec.N-ary

module Easy where

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
  blooper = run 3 (λ x y z → x ∷ y ∷ z ∷ x ∷ y ∷ [])  

    -- x is fin 0, y is fin 1, z in fin 2

-- Trickier example (which does not work!)

open import Data.Product renaming (map to _⋆_)

module Tricky (ops : ℕ)               -- operators (minus one!!)
              (as  : Vec ℕ ops) -- arities of operators
              where

  open import Data.Nat as Nat
    using (ℕ; zero; suc; z≤n; s≤s)
    renaming ( _+_ to _N+_; _∸_ to _N∸_
             ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_)

  data Expr : Set where
    op : (x : Fin ops) → Vec Expr (lookup x as) → Expr

  incr : ∀ {m n} → m N≤ n → m N≤ suc n
  incr z≤n = z≤n
  incr (s≤s m≤n) = s≤s (incr m≤n)

  dropp : ∀ {m n} → suc m N≤ n → m N≤ n
  dropp (s≤s m≤n) = incr m≤n

  refly : ∀ {m} → m N≤ m
  refly {zero} = z≤n
  refly {suc n} = s≤s refly

-- The underlying type
  run-type : (n : ℕ) → n N≤ ops → Set₁
  run-type zero    p = Set
  run-type (suc n) p = (Vec Expr (lookup (fromℕ≤ p) as) → Expr) → run-type n (dropp p)

-- ∀ⁿ
  runs : (n : ℕ) (p : n N≤ ops) → run-type n p → Set
  runs zero    p P = P
  runs (suc n) p P = ∀ x → runs n (dropp p) (P x)

-- Returning an Expr
  runt : (n : ℕ) (p : n N≤ ops) → run-type n p
  runt zero    p = Expr
  runt (suc n) p = λ x → runt n (dropp p)

-- Running it
  run : (n : ℕ) (p : n N≤ ops) → runs n p (runt n p) → Expr
  run zero    p = λ xs → xs
  run (suc n) p = λ f → run n (dropp p) (f (op (fromℕ≤ p)))

-- Starting from the beginning
  build : runs ops refly (runt ops refly) → Expr
  build = run ops refly
  
module Example where

  open Tricky 3 (2 ∷ 1 ∷ 0 ∷ []) public

  e : Expr
  e = build (λ ε _⁻¹ _∙_ → {!!})


  
