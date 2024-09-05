module Context.Base where
    
open import Agda.Primitive
open import Data.List.Base public

open import Data.Nat.Base

-- Term --------------------------------------------------------------


infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infixl 7  _`+_
infixl 8  _`*_
infix 9  `_ 

data Type : Set where
  ★ : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A


data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ X}
    → Γ ∋ X
      -----
    → Γ ⊢ X

  ƛ_  :  ∀ {Γ X}
    → Γ , X ⊢ X
      ---------
    → Γ ⊢ X

  _`+_ : ∀ {Γ X}
    → Γ ⊢ X
    → Γ ⊢ X
      ------
    → Γ ⊢ X

  _`*_ : ∀ {Γ X}
    → Γ ⊢ X
    → Γ ⊢ X
      ------
    → Γ ⊢ X

