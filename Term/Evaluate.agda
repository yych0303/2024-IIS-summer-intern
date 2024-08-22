{-# OPTIONS --allow-unsolved-metas #-}
module Term.Evaluate where

open import Agda.Primitive

open import Term.Base
open import Ring.Base
open import Ring.Operations

module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  infix 1 eval

  {-# NON_TERMINATING #-}
  eval : Term R → R
  eval term with term
  ...          | (` v)            = v
  ...          | ($ i)            = R0   -- not possible
  ...          | (t `+ t₁)        = (eval t) R+ (eval t₁)
  ...          | (t `* t₁)        = (eval t) R* (eval t₁)
  ...          | `P[ t , t₁ ]     = rP ring (eval t) (eval t₁)
  ...          | `C[ t , t₁ ]     = rC ring (eval t) (eval t₁)
  ...          | (`Σ[ i ∈ l ] t)  = rsigma ring l (λ v → eval ([ i := v ] t))
  ...          | (`Π[ i ∈ l ] t)  = rpi ring l (λ v → eval ([ i := v ] t))
  ...          | [ t ]`!          = r! ring (eval t)