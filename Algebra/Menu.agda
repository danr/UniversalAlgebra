{-# OPTIONS --universe-polymorphism #-}
module Algebra.Menu where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function

Op : ∀ {i} → ℕ → Set i → Set i
Op zero    A = A
Op (suc n) A = A → Op n A

{-
Monoid : ∀ {c} (X : Set c) → X → Op 2 X → Structure c
Monoid S = structure S 
                     2 -- operators
                     3 -- laws
                     ( 0 ∷ 2 ∷ [] ) -- one unary and one binary operator
                                    -- tag these / build expr tree so you cannot use something else?
                     (λ ε _∙_ →   (3 , λ x y z → (x ∙ (y ∙ z)) == ((x ∙ y) ∙ z)  ) 
                                ∷ (1 , λ x     → (x ∙ ε) == x                    )
                                ∷ (1 , λ x     → (ε ∙ x) == x                    )
                                ∷ [])
                     )
-}

module Test₃ where

  module Builder {c} (X : Set c)  -- underlying set
                 (ops : ℕ)        -- number of operators 
                 (laws : ℕ)       -- number of laws
                 (α : Vec ℕ ops)  -- arities of operators
                 where
    
    data Expr (n : ℕ) : Set where
      var : (x : Fin n) → Expr n
      op  : (op : Fin ops) (args : Vec (Expr n) (lookup op α)) → Expr n

    module Law (args : ℕ) where

      data Equality : Set where
        _==_ : (lhs rhs : Expr args) → Equality

      Env : ℕ → Set
      Env = Vec (Expr args)

      builder-type : (n : ℕ) → N-ary n (Expr args) Set
      builder-type zero    = Equality
      builder-type (suc n) = λ i → builder-type n

      builder : (n : ℕ) → Env n → ∀ⁿ n (builder-type n) → Equality
      builder zero    []       = λ xs → xs
      builder (suc n) (x ∷ xs) = λ f → builder n xs (f x)

      build-type : N-ary args (Expr args) Set
      build-type = builder-type args

      build : ∀ⁿ args build-type → Equality
      build = builder args (map var (allFin args))

    open Law public using (Equality ; build ; _==_) 

    Env : ℕ → Set
    Env = Vec (Fin ops)

    enter-type : (n : ℕ) → N-ary n (Fin ops) Set
    enter-type zero    = Vec (∃ Equality) laws
    enter-type (suc n) = λ i → enter-type n

    enter : (n : ℕ) → Env n → ∀ⁿ n (enter-type n) → Vec (∃ Equality) laws
    enter zero    []       = λ xs → xs
    enter (suc n) (x ∷ xs) = λ f → enter n xs (f x)

    structure : ∀ⁿ ops (enter-type ops) → Vec (∃ Equality) laws
    structure = enter ops (allFin ops) -- (map op (allFin ops)) 


  open Builder public 

  test : ∀ {i} (X : Set i) → {!!}
  test {i} X = build X 2 1 (0 ∷ 2 ∷ []) 2 (λ x y → x == y)
 
{-
 
  Monoid : ∀ {c} (X : Set c) → Vec
                                 (Σ ℕ
                                  (Equality X 2 3 (0 ∷ 2 ∷ []))) 3
  Monoid S = structure S 2 3 ( 0 ∷ 2 ∷ [] ) 
                         (λ ε _∙_ → (3 , build S 2 3 (0 ∷ 2 ∷ []) 3 (λ x y z → {!!} == {!!})) 
                                  ∷ {!!}) 

-}

{-structure S 
                       2 -- operators
                       3 -- laws
                       ( 0 ∷ 2 ∷ [] ) -- one unary and one binary operator
                                    -- tag these / build expr tree so you cannot use something else?
                       (λ ε _∙_ → ? {-  (3 , λ x y z → (x ∙ (y ∙ z)) == ((x ∙ y) ∙ z)  ) 
                                  ∷ (1 , λ x     → (x ∙ ε) == x                    )
                                  ∷ (1 , λ x     → (ε ∙ x) == x                    )
                                  ∷ []) -})
                 -}    

  
{-
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

-}
