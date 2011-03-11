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
open import Data.Fin renaming (_<_ to _<Fin_ ; _≤_ to _≤Fin_)
open import Data.Vec
open import Data.Product renaming (map to _⋆_)
open import Data.Vec.N-ary
open import Function
open import Data.ParallelVector
open import Data.ParallelList

-- Increasing the right side of ≤
_++ : ∀ {m n} → m ≤ n → m ≤ suc n
_++ z≤n = z≤n
_++ (s≤s m≤n) = s≤s (m≤n ++)

-- Decreasing the left hand side of ≤
↓_ : ∀ {m n} → suc m ≤ n → m ≤ n
↓_ (s≤s m≤n) = m≤n ++

-- Reflexivity of ≤
m≤m : ∀ {m} → m ≤ m
m≤m {zero} = z≤n
m≤m {suc n} = s≤s m≤m

Op : ∀ {i} → ℕ → Set i → Set i 
Op zero    A = A
Op (suc n) A = A → Op n A 

apply : ∀ {i} {X : Set i} (n : ℕ) → Op n X → Vec X n → X
apply zero    f []       = f
apply (suc n) f (x ∷ xs) = apply n (f x) xs

makeOp : ∀ {i} {X : Set i} (n : ℕ) → (Vec X n → X) → Op n X
makeOp zero    f = f []
makeOp (suc n) f = λ x → makeOp n (λ xs → f (x ∷ xs))

module Builder (arities : List ℕ) where

  ops : ℕ
  ops = length arities
  
  α : Vec ℕ ops
  α = fromList arities
  
  data Expr (v : ℕ) : Set where
    var : (x : Fin v) → Expr v
    op  : (x : Fin ops) (args : Vec (Expr v) (lookup x α)) → Expr v

  data Equality (v : ℕ) : Set where
    _==_ : (lhs rhs : Expr v) → Equality v

  Env : (v n : ℕ) → Set
  Env v n = Vec (Expr v) n

  law-type : (v n : ℕ) → Set₁
  law-type v zero    = Set
  law-type v (suc n) = Expr v → law-type v n

  law-run′ : (v n : ℕ) → law-type v n
  law-run′ v zero    = Equality v
  law-run′ v (suc n) = λ i → law-run′ v n

  law-∀ : (v n : ℕ) → law-type v n → Set
  law-∀ v zero    P = P
  law-∀ v (suc n) P = (x : Expr v) → law-∀ v n (P x)

  law-run″ : (v n : ℕ) → Env v n → law-∀ v n (law-run′ v n) → Equality v
  law-run″ v zero    Γ        = λ xs → xs
  law-run″ v (suc n) (x ∷ xs) = λ f → law-run″ v n xs (f x)

  law-run : (v : ℕ) → law-∀ v v (law-run′ v v) → Equality v
  law-run v = law-run″ v v (Data.Vec.map var (allFin v))

  -- Arity of an operator, indexed by a comparison
  arity : ∀ {n} → n < ops → ℕ
  arity p = lookup (fromℕ≤ p) α

  -- The underlying type
  type : (n : ℕ) (p : n ≤ ops) → Set₁
  type zero    p = Set 
  type (suc n) p = (∀ {v} → Op (arity p) (Expr v)) → (type n (↓ p)) 
   
  -- Quantification over the type
  ∀′ : (n : ℕ) (p : n ≤ ops) → type n p → Set
  ∀′ zero    p P = P
  ∀′ (suc n) p P = (op : ({v : ℕ} → Op (arity p) (Expr v))) → ∀′ n (↓ p) (P op)

  -- The runner type
  run-type : (n : ℕ) (p : n ≤ ops) → type n p
  run-type zero    p = List (∃ λ v → (law-∀ v v (law-run′ v v)))
  run-type (suc n) p = λ f → run-type n (↓ p) 

  -- Runner
  run : (n : ℕ) (p : n ≤ ops) → ∀′ n p (run-type n p) → List (∃ Equality) 
  run zero    p = λ xs → Data.List.map (λ x → proj₁ x , law-run (proj₁ x) (proj₂ x) ) xs
  run (suc n) p = λ f → run n (↓ p) (f (λ {v} → makeOp (arity p) (op {v} (fromℕ≤ p))))

  -- To build, start from the beginning
  build : ∀′ ops m≤m (run-type ops m≤m) → List (∃ Equality)
  build = run ops m≤m

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


module Test where
  
  open Builder (1 ∷ 2 ∷ [])
 
  laws : List (∃ Equality)
  laws = build (λ _+_ -_ → (3 , λ x y z → (x + y) == - z)
                         ∷ (4 , λ x y z w → ((x + y) + (z + w)) == ((- (z + x)) + - w) ) 
                         ∷ (3 , λ x y z → (x + y) == - (y + z))
                         ∷ [])


record Structure : Set where
  field 
    arities   : List ℕ 

  open Builder arities

  field 
    laws      : List (∃ Equality) 

  open Builder arities public

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
    ⟦law⟧ : ParList (λ x → (xs : Vec X (proj₁ x)) → ⟦ proj₂ x ⟧′ xs) laws

-- This friendly little function does not work too well :(

module ImplicitBuilder {arities : List ℕ} where
  open Builder arities public using (build ; Expr ; Equality ; _==_)

open ImplicitBuilder public

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

