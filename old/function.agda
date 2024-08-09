open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)



-- Define what it means for two functions to be inverses
record _InverseOf_ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    left-inverse  : ∀ x → g (f x) ≡ x
    right-inverse : ∀ y → f (g y) ≡ y

-- Define a bijection between A and B
record Bijection {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to   : A → B
    from : B → A
    inverse : to InverseOf from

-- Shorthand for existence of a bijection
_↔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A ↔ B = Bijection A B