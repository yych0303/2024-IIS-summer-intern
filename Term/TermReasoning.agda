module Term.TermReasoning where
{-

  Term R -- trns funcRℕ -> Term ℕ
    |                        |
    |                        |
eval ringR               eval ringℕ
    |                        |
    V                        V
    R ------- funcRℕ ------> ℕ

 ta ≈ᴿ tb <----- ? -----> tn ≈ᴺ tm
    Λ                        Λ
    |                        |
  ringR                    ringℕ
    |                        |
    V                        V 
  a ≃ b - _=[funcRℕ]_⇒ -> n ≡ m

-}

open import Agda.Primitive
open import Term.Base
open import Term.Eval
open import Ring.Base
-- open import Relation.Binary.Core
-- open import Relation.Binary.Bundles

private    
  variable 
    c ℓ : Level

module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  infix 0 _≈_

  _≈_ : Term R → Term R → Set ℓ
  _≈_ ta tb = eval ring ta ≃ eval ring tb
  
  
  ≈-refl : ∀ {ta : Term R}
      -----
    → ta ≈ ta
  ≈-refl {ta} = refl {eval ring ta}

  ≈-sym : ∀ {ta tb : Term R}
    → ta ≈ tb
      -----
    → tb ≈ ta
  ≈-sym ta≈tb = sym ta≈tb

  ≈-trans : ∀ {ta tb tc : Term R}
    → ta ≈ tb
    → tb ≈ tc
      -----
    → ta ≈ tc
  ≈-trans ta≈tb tb≈ta = trans ta≈tb tb≈ta


  module ≈-Reasoning where

    infix  1 ≈-begin_
    infixr 2 _≈⟨_⟩_
    infix  3 _≈-∎

    ≈-begin_ : ∀ {ta tb tc : Term R}
      → ta ≈ tb
        -----
      → ta ≈ tb
    ≈-begin ta≈tb = ta≈tb

    _≈⟨_⟩_ : ∀ (ta : Term R) {tb tc : Term R}
      → ta ≈ tb
      → tb ≈ tc
        -----
      → ta ≈ tc
    ta ≈⟨ ta≈tb ⟩ tb≈tc = ≈-trans ta≈tb tb≈tc

    _≈-∎ : ∀ (ta : Term R)
        -----
      → ta ≈ ta
    ta ≈-∎ = ≈-refl

  open ≈-Reasoning

  