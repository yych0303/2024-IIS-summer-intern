{-# OPTIONS --allow-unsolved-metas #-}
module Term.Evaluate where

open import Agda.Primitive

open import Term.Base
open import Ring.Base
open import Ring.Operations

module _ {ℓ : Level} {ring : Ring {ℓ}} where
  open Ring ring

  infix 1 eval


  eval : Term ring → R
  eval (` x) = x                    
  eval (t `+ t₁) = (eval t) R+ (eval t₁)
  eval (t `* t₁) = (eval t) R* (eval t₁)

