{-# OPTIONS --safe --cubical  #-}


module _ where

open import Cubical.Foundations.Prelude 

open import Cubical.Foundations.HLevels

private
  variable
    ℓ     : Level
    A B C : Set ℓ
    P     : A → Set ℓ
    x y   : A
    p q   : x ≡ y

infix 7 _∈′_
infix 7 _∈_
infix 7 _∉_
--infix 6 _∉′_
infix 7 _⊆_

data K (A : Set ℓ) : Set ℓ where
  ∅     : K A
  [_]   : A → K A
  _∪_   : K A → K A → K A
  nl    : ∀ x → ∅ ∪ x ≡ x
  nr    : ∀ x → x ∪ ∅ ≡ x
  idem  : ∀ a → [ a ] ∪ [ a ] ≡ [ a ]
  assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  com   : ∀ x y → x ∪ y ≡ y ∪ x
  trunc : isSet (K A)
infixr 10 _∪_

-- Membership relation

data _∈′_ {A : Set ℓ} (a : A) : (x : K A) → Set ℓ where
  here  : a ∈′ [ a ]
  left  : ∀ {x y} → (a∈x : a ∈′ x) → a ∈′ x ∪ y
  right : ∀ {x y} → (a∈y : a ∈′ y) → a ∈′ x ∪ y
  sq    : ∀ {x}   → isProp (a ∈′ x)
  
_∈_ : (a : A) → K A → hProp
a ∈ x = a ∈′ x , sq


_⊆_ : K A → K A → hProp
x ⊆ y = ∀[ a ] a ∈ x ⇒ a ∈ y