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

module Tricky (ops : ℕ)        -- operators 
              (as  : Vec ℕ ops) -- arities of operators
              where

  data Expr : Set where
    op : (x : Fin ops) → Vec Expr (lookup x as) → Expr

  Elem : Set
  Elem = ∃ λ i → Vec Expr (lookup i as) → Expr
  -- also tried 
  -- Elem = ∀ {i} → Vec Expr (lookup {i} as) → Expr

  Env : ℕ → Set
  Env = Vec Elem

  run-type : (n : ℕ) → N-ary n Elem Set
  run-type zero    = Expr
  run-type (suc n) = λ f → run-type n

  run : (n : ℕ) → Env n → ∀ⁿ n (run-type n) → Expr
  run zero    []       = λ e → e
  run (suc n) (x ∷ xs) = λ f → run n xs (f x)

  -- The problem is that inside the function build creates,
  -- it is now known that the fins are mapped to 0..op-1,
  -- so we really need to build some step after this
  build : ∀ⁿ ops (run-type ops) → Expr
  build = run ops (map (λ i → i , (op i)) (allFin ops))  

module Example where

  open Tricky 3 (0 ∷ 1 ∷ 2 ∷ []) public

  e : Expr
  e = build (λ ε ⁻¹ _∙_ → proj₂ ε {!!} )


  
