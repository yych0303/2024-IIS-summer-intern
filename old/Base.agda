module Context.Base where
    
open import Agda.Primitive
open import Data.List.Base public

open import Data.Nat.Base

open import Ring.Base

module _  {ℓ : Level} (ring : Ring {ℓ} ) where
  open Ring ring

  infix  4  _⊢_
  infix  4  _∋_
  infixl 5  _,_

  infix  6  ƛ_
  infix  6  `_
  infixl 7  _`+_
  infixl 7  _`*_



  data Context : Set ℓ where
    ∅   : Context
    _,_ : Context → R → Context

  data _∋_ : Context → R → Set ℓ where

    Z : ∀ {Γ A}
      ---------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ , B ∋ A
  
Γ : List FinSet

t : Term

_⊢_ : Context → Term  → Set

Γ ⊢ t

[t]  [u]

  data _⊢_ : Context → Term → Set where

    `_ : ∀ {Γ A}
      → Γ ∋ A
        -----
      → Γ ⊢ A

    ƛ_  :  ∀ {Γ}
      → Γ , ★ ⊢ ★
        ---------
      → Γ ⊢ ★

    _·_ : ∀ {Γ}
      → Γ ⊢ ★
      → Γ ⊢ ★
        ------
      → Γ ⊢ ★