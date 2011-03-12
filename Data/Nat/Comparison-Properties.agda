module Data.Nat.Comparison-Properties where

open import Data.Nat 

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

