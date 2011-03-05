module Equalizer where

open import Function using (_∘_ ; const)
open import Relation.Binary.PropositionalEquality 
  using (_≡_ ; _≗_ ; refl ; subst ; proof-irrelevance)

Monic : {X Y : Set} → (X → Y) → Set₁
Monic {X} f = {Z : Set} (x y : Z → X) → f ∘ x ≗ f ∘ y → x ≗ y

-- In the category Agd (for the want of a better name) of Agda types 
-- and functions, an injective function is monic.
Injective : {X Y : Set} → (X → Y) → Set
Injective f = ∀ x y → f x ≡ f y → x ≡ y

M→I : {X Y : Set} → (f : X → Y) → Monic f → Injective f
M→I f monic x y eq = monic (const x) (const y) (const eq) eq

I→M : {X Y : Set} → (f : X → Y) → Injective f → Monic f
I→M f inj g h eq x = inj (g x) (h x) (eq x)

module Equalizer {A B : Set} (f g : A → B) where

{-

   An equalizer of f,g : A ⇉ B consists of an object E and an arrow i : E → A
   such that f ∘ i = g ∘ i.

   Futhermore, this construct is universal so if we have an object Z and an
   arrow γ : Z → A such that f ∘ γ = g ∘ γ then there exists an unique arrow
   u : Z → E such that i ∘ u = γ.

   Illustration:

           i        f
       E -----> A =====⇉ B
       ⇡     ↗      g
       ⋮    /    
     u ⋮   /    
       ⋮  / γ
       ⋮ /
       Z


-}

  data E : Set where
    elem : (x : A) → (eq : f x ≡ g x) → E

  i : E → A
  i (elem x eq) = x

  equalises : f ∘ i ≗ g ∘ i 
  equalises (elem x eq) = eq

  -- The inclusion is always monic.
  i-inj : Injective i
  i-inj (elem x eq) (elem .x eq') refl = 
    subst (λ eq′ → elem x eq ≡ elem x eq′) (proof-irrelevance eq eq') refl

  i-monic : Monic i
  i-monic = I→M i i-inj

  -- The universal property
  module Universal {Z : Set} (γ : Z → A) (u-eq : f ∘ γ ≗ g ∘ γ) where

    u : Z → E
    u z = elem (γ z) (u-eq z)

    u-commute : i ∘ u ≗ γ
    u-commute z = refl

    u-unique : (u′ : Z → E) → i ∘ u′ ≗ γ → u′ ≗ u
    u-unique u′ u′-eq z = i-inj (u′ z) (u z) (u′-eq z)

  open Universal public

open Equalizer public
