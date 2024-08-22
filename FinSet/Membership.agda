{-# OPTIONS --allow-unsolved-metas #-}
module FinSet.Membership where
    
open import Agda.Primitive
open import Data.List.Base public
open import Relation.Nullary using (¬_) public
open import Data.Empty

module _ {i : Level} {A : Set i} where

  infix 7 _∈_
  infix 7 _∉_
  infix 7 _∈₁_
 
  data _∈_ (a : A) : (x : List A) → Set i where
    here  : ∀ {x} → a ∈ (a ∷ x)
    there : ∀ {b} {x} → (a∈x : a ∈ x) → a ∈ (b ∷ x)
    
  _∉_ : (a : A) → (x : List A) → Set i
  a ∉ x = ¬ (a ∈ x)
  
  data _∈₁_ (a : A) : (x : List A) → Set i where
    here₁  : ∀ {x} → (a∉x : a ∉ x) → a ∈₁ (a ∷ x) 
    there₁ : ∀ {b x} → (a∉b : a ∉ [ b ]) → (a∈₁x : a ∈₁ x) → a ∈₁ (b ∷ x)

  -- Some Propersitions

  Exist : List A → Set _
  Exist list = (aₑ : A) → aₑ ∈ list
  
  Once : List A → Set _ 
  Once list = (a₁ : A) → a₁ ∈ list → a₁ ∈₁ list
  
  Contain : List A → List A → Set _
  Contain list l = (a : A) → (a ∈ list) → a ∈ l
  
  ------------------------------------------------------------------------------------------------------------------

  remove : (a : A) → (x : List A) → (a∈x : a ∈ x) → List A
  remove a .(a ∷ x) (here {x = x}) = x
  remove a .(b ∷ x) (there {b = b} {x = x} a∈x) = b ∷ remove a x a∈x

  ∈-remove  : ∀ {b c : A} {l : List A}
              → (b∈l : b ∈ l)
              → (c∈l : c ∈ l)
              → (c∉b : c ∉ [ b ])
              → (c ∈ (remove b l b∈l))
  ∈-remove here here c∉b = ⊥-elim (c∉b here)
  ∈-remove here (there c∈l) c∉b = c∈l
  ∈-remove (there b∈l) here c∉b = here
  ∈-remove (there b∈l) (there c∈l) c∉b = there (∈-remove b∈l c∈l c∉b)
