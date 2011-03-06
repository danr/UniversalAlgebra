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

module Test₂ where
  
  arity : ∀ {i} {A : ℕ → Set i} {n} → Fin n → Vec (Σ ℕ A) n → ℕ → Set
  arity m xs n = proj₁ (lookup m xs) ≡ n

  data Law {c} {γ} (S : Set c) (Γ : Vec (∃ (λ n → Op n S)) γ) : ℕ → Set c where
    Associative : (mul : Fin γ) → arity mul Γ 2 → Law S Γ 3
    Commutative : (mul : Fin γ) → arity mul Γ 2 → Law S Γ 2
    LeftIdentity RightIdentity : (mul  : Fin γ) → arity mul  Γ 2 
                               → (unit : Fin γ) → arity unit Γ 0 → Law S Γ 1

  ⟦_,_,_⟧ˡ : ∀ c ℓ → ℕ → Level
  ⟦ c , ℓ , zero  ⟧ˡ = ℓ
  ⟦ c , ℓ , suc n ⟧ˡ = c ⊔ ⟦ c , ℓ , n ⟧ˡ

  ⟦_,_⟧ : ∀ {c ℓ} {S : Set c} {n} Γ → Law S Γ n → Rel S ℓ → Set ⟦ c , ℓ , n ⟧ˡ
  ⟦ Γ , Associative   mul am         ⟧ _≈_ = {!!} -- ∀ x y z → (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z) 
  ⟦ Γ , Commutative   mul am         ⟧ _≈_ = {!!} -- ∀ x y   → (x ∙ y) ≈ (y ∙ x) 
  ⟦ Γ , LeftIdentity  mul am unit au ⟧ _≈_ = {!!} -- ∀ x     → (x ∙ ε) ≈ x
  ⟦ Γ , RightIdentity mul am unit au ⟧ _≈_ = {!!} -- ∀ x     → (ε ∙ x) ≈ x
  

  record Structure c : Set (suc c) where
    field 
      S         : Set c
      ops       : ℕ
      operators : Vec (∃ (λ n → Op n S)) ops
      eqns      : ℕ
      laws      : Vec (∃ (Law S operators)) eqns 

{-
Monoid : ∀ {c} (X : Set c) → X → Op 2 X → Structure c
Monoid S = structure S 
                     2 -- operators
                     3 -- laws
                     ( 0 ∷ 2 ∷ [] ) -- one unary and one binary operator
                                    -- tag these / build expr tree so you cannot use something else?
                     (λ ε _∙_ →   λ x y z → (x ∙ (y ∙ z)) == ((x ∙ y) ∙ z)   
                                ∷ λ x     → (x ∙ ε) == x
                                ∷ λ x     → (ε ∙ x) == x
                                ∷ [])
                     )
-}

module Test₃ where

  module Builder {c} (X : Set c)  -- underlying set
                 (ops : ℕ)        -- number of operators 
                 (α : Vec ℕ ops)  -- arities of operators
                 where
    
    data Expr (n : ℕ) : Set where
      var : (x : Fin n) → Expr n
      op  : (op : Fin ops) (args : Vec (Expr n) (lookup op α)) → Expr n

    Laws : ℕ → Set
    Laws zero    = {!!}
    Laws (suc n) = {!!}

    UnderOps : ∀ {n} → Vec ℕ n → ℕ → Set
    UnderOps []       laws = Laws laws
    UnderOps (x ∷ xs) laws = {!!}

--    structure = 


{-
  structure : ∀ {c} (X : Set c) 
              (ops : ℕ) (eqns : ℕ) (arities : Vec ℕ ops) → 
  structure = Rest X ops eqns arities
  -}
     
{-
  Monoid : ∀ {c} (X : Set c) → X → Op 2 X → Structure c
  Monoid S ε _∙_ = record 
    { S = S
    ; ops = 2
    ; operators = (0 , ε) ∷ (
-}

module Test₁ where
  record Structure c : Set (suc c) where
    field 
      S             : Set c
      ops           : ℕ
      operators     : Vec (Σ ℕ (λ n → Op n S)) ops
      eqns          : ℕ
      laws          : Vec (Σ ℕ (λ n → Op n S × Op n S)) eqns
   
  ∣_∣ : ∀ {c} → Structure c → Set c
  ∣_∣ = Structure.S
   
  _==_ : ∀ {i} {X : Set i} → X → X → X × X
  x == y = x , y
   
  Monoid : ∀ {c} (X : Set c) → X → Op 2 X → Structure c
  Monoid S ε _∙_ = record 
    { S = S
    ; ops = 2
    ; operators = (0 , ε) ∷ (2 , _∙_) ∷ []
    ; eqns = 3
    ; laws = (3 , (λ x y z → x ∙ (y ∙ z)) 
                == λ x y z → (x ∙ y) ∙ z) 
           ∷ (1 , ((λ x → x ∙ ε) 
                == (λ x → ε))) 
           ∷ (1 , ((λ x → ε ∙ x) 
                == (λ x → ε))) 
           ∷ []
    }
   
  module Extraction {c ℓ} (struct : Structure c) (_≈_ : Rel ∣ struct ∣ ℓ) where
   
    open Structure struct 
   
    extract-level : (n : ℕ) → Level
    extract-level zero    = ℓ
    extract-level (suc n) = c ⊔ extract-level n
   
    extract-law : (n : ℕ) → Op n S × Op n S → Set (extract-level n)
    extract-law zero    (lhs , rhs) = lhs ≈ rhs
    extract-law (suc n) (lhs , rhs) = (x : S) → extract-law n (lhs x , rhs x)

{-

this is what I have in mind:

monoid : (S : Setoid) (ε : Constant S) (_∙_ : Op₂ S) → Structure c ℓ
monoid S ε _∙_ = structure on S
            2 operators∶ ε   (constant) 
                         _∙_ (arity∶ 2) 
            3 laws∶ (Associative _∙_)
                    (LeftIdentity _∙_ ε)
                    (RightIdentity _∙_ ε)

-}

    