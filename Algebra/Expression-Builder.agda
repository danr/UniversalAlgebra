------------------------------------------------
--
-- Making expressions
--

-- Todo: remove <, ≤ and use Fins and
-- inject₁ : {m' : ℕ} → Fin m' → Fin (suc m')
-- instead.
--
-- Todo: make the operators appear in right order

{-# OPTIONS --universe-polymorphism #-}
module Expression-Builder where

open import Data.Nat as Nat hiding (_⊔_)
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Vec
open import Data.Vec.N-ary
open import Level

module Builder (ops : ℕ)         -- operators 
               (as  : Vec ℕ ops) -- arities of operators
               where

  -- Expression datatype
  data Expr : Set where
    op : (x : Fin ops) → Vec Expr (lookup x as) → Expr

  -- Arity of an operator, indexed by a comparison
  arity : ∀ {n} → n < ops → ℕ
  arity p = lookup (fromℕ≤ p) as

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

  -- The underlying level
  level : (ℓ : Level) (n : ℕ) (p : n ≤ ops) → Level
  level ℓ zero    p = ℓ
  level ℓ (suc n) p = N-ary-level zero zero (arity p) ⊔ level ℓ n (↓ p)

  -- The underlying type
  type : (n : ℕ) (p : n ≤ ops) → Set (level (suc zero) n p) 
  type zero    p = Set
  type (suc n) p = (N-ary (arity p) Expr Expr) → (type n (↓ p)) 
     
  -- Quantification over the type
  ∀′ : (n : ℕ) (p : n ≤ ops) → type n p → Set (level zero n p)
  ∀′ zero    p P = P
  ∀′ (suc n) p P = ∀ (xs : N-ary (arity p) Expr Expr) → ∀′ n (↓ p) (P xs) 

  -- The runner type
  run-type : (n : ℕ) (p : n ≤ ops) → type n p
  run-type zero    p = Expr
  run-type (suc n) p = λ f → run-type n (↓ p) 

  -- Runner
  run : (n : ℕ) (p : n ≤ ops) → ∀′ n p (run-type n p) → Expr
  run zero    p = λ xs → xs
  run (suc n) p = λ f → run n (↓ p) (f (curryⁿ (op (fromℕ≤ p))))

  -- To build, start from the beginning
  build : ∀′ ops m≤m (run-type ops m≤m) → Expr
  build = run ops m≤m
  
module Example where

  open Builder 3 (1 ∷ 2 ∷ 0 ∷ []) public  
  -- 3 operators, arities are 0, 2 and 1

  -- An expression!
  e : Expr     
  e = op zero ((op (suc zero) 
                   ((op (suc (suc zero)) []) ∷ ((op (suc (suc zero)) []) ∷ []))) ∷ [])
  
  e₂ : Expr
  e₂ = build (λ #0 _+_ -_ → - (#0 + #0))

module Example₂ where
  
  open Builder 5 (3 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ []) public
  
  e : Expr
  e = build (λ _∨_ _∧_ true false if_then_else_ → 
            if true ∧ false then true ∨ true else false)



