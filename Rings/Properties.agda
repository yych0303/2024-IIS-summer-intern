module Rings.Properties where

open import Agda.Primitive
open import Rings.CommutativeRing


module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  -- zero-identity+r : ∀ {x : R} → (R0 R+ x) ≃ x
  -- zero-identity+r {x} = {!   !}
  -- head-01         : ∀ {x : R} → ((x ≃ R0) ⊎ (x ≃ R1)) ↔ (Rhead x ≃ x) 