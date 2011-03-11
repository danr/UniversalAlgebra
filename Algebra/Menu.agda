-----------------
--
-- Work in progress!!
--
-----------------

{-# OPTIONS --universe-polymorphism #-}
module Algebra.Menu where

open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality renaming (setoid to Set→Setoid)
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function
open import Data.ParallelVector
open import Data.ParallelList

Op : ∀ {i} → ℕ → Set i → Set i
Op zero    A = A
Op (suc n) A = A → Op n A

apply : ∀ {i} {X : Set i} n → Op n X → Vec X n → X
apply zero    f []       = f
apply (suc n) f (x ∷ xs) = apply n (f x) xs

{-
Monoid : Structure
Monoid = structure 
                     2 -- operators
                     3 -- laws
                     ( 0 ∷ 2 ∷ [] ) -- one constant and one binary operator
                     (λ ε _∙_ →   (3 , λ x y z → (x ∙ (y ∙ z)) == ((x ∙ y) ∙ z)  ) 
                                ∷ (1 , λ x     → (x ∙ ε) == x                    )
                                ∷ (1 , λ x     → (ε ∙ x) == x                    )
                                - [])
                     )
-}

module Builder (ops : ℕ)        -- number of operators 
               (α : Vec ℕ ops)  -- arities of operators
               (laws : ℕ)       -- number of laws
               where
  
  data Expr (n : ℕ) : Set where
    var : (x : Fin n) → Expr n
    op  : (x : Fin ops) (args : Vec (Expr n) (lookup x α)) → Expr n

  module Law (args : ℕ) where

    data Equality : Set where
      _==_ : (lhs rhs : Expr args) → Equality

  open Law public using (Equality ; _==_) 

  Env : ℕ → Set
  Env = Vec (Fin ops)

  enter-type : (n : ℕ) → N-ary n (Fin ops) Set
  enter-type zero    = Vec (∃ Equality) laws
  enter-type (suc n) = λ i → enter-type n

  enter : (n : ℕ) → Env n → ∀ⁿ n (enter-type n) → Vec (∃ Equality) laws
  enter zero    []       = λ xs → xs
  enter (suc n) (x ∷ xs) = λ f → enter n xs (f x)

  structure : ∀ⁿ ops (enter-type ops) → Vec (∃ Equality) laws
  structure = enter ops (allFin ops)

  module Interpret c ℓ (setoid : Setoid c ℓ) 
                       (⟦op_⟧ : (x : Fin ops) → Op (lookup x α) (Setoid.Carrier setoid)) where
    open Setoid setoid renaming (Carrier to X)

    -- Termination checker rewritage
    mutual
      φ : ∀ {m n} → Vec (Expr n) m → Vec X n → Vec X m
      φ []       Γ = []
      φ (e ∷ es) Γ = ⟦ e ⟧ Γ ∷ φ es Γ

      ⟦_⟧ : ∀ {n} → Expr n → Vec X n → X
      ⟦ var x ⟧     Γ = lookup x Γ
      ⟦ op x args ⟧ Γ = apply (lookup x α) ⟦op x ⟧ (φ args Γ)
    
    ⟦_⟧′ : ∀ {n} → Equality n → Vec X n → Set ℓ
    ⟦ lhs == rhs ⟧′ Γ = ⟦ lhs ⟧ Γ ≈ ⟦ rhs ⟧ Γ

record Structure : Set where
  field  
    arities   : List ℕ
    arguments : List ℕ 

  #ops  = length arities 
  #laws = length arguments

  open Builder #ops (fromList arities) #laws

  field
    laws      : ParList Equality arguments

  open Builder #ops (fromList arities) #laws public

record Instance c ℓ (S : Structure) : Set (suc (c ⊔ ℓ)) where
  open Structure S

  field
    setoid : Setoid c ℓ

  open Setoid setoid renaming (Carrier to X)
  
  -- easy to work with (in the interpreter), hard to instantiate
  field
    ⟦op⟧ : ParVec (λ n → Op n X) (fromList arities)

  open Interpret c ℓ setoid (par-lookup ⟦op⟧)

  -- easy to define, hard to instantiate
  field
    ⟦law⟧ : ParVec (λ x → (xs : Vec X (proj₁ x)) → ⟦ proj₂ x ⟧′ xs) (toFlatVec laws)

-- Sketch of projection formulas
{-
module Projection {c ℓ} {S : Structure} (I : Instance c ℓ S) where

  open Structure S
  open Instance I

  c₀ : {0 ∈ arities} → Carrier
  c₀ {here} = ...
  
  c₁ : {0 ∈₂ arities} → Carrier

  _+_ bin₀ _∙_ : {2 ∈ arities} → Op 2 Carrier

  _*_ bin₁     : {2 ∈₂ arities} → Op 2 Carrier

  -_ _⁻¹ : {1 ∈ arities} → Op 1 Carrier

  if_then_else_ _⟨_⟩_ _?_∶_   -- i don't know any used ternary operators really ^^

  law : (n : ℕ) → {p : n < #laws} → ∀ⁿ x (Law (lookup (fromℕ p) arities))
  
  assoc assoc-+ assoc₀ : {p : Associative ∈̂ laws} → ...

  -- given a concrete structure and an instance, these implicit arguments
  -- can be automatically inferred (oh shit, actually they probably can't)
  -- maybe only the < one or maybe not even that one... hmm
  -- but I guess if you write a decision procedure! and pattern matches
  -- on that it returns yes instead. hmm. that's probably it.
-}

