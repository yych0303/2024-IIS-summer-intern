{-# OPTIONS --allow-unsolved-metas #-}
module Term.Evaluate where

open import Agda.Primitive
open import Data.Nat using (ℕ)

open import Term.Base
open import Ring.Base
open import Ring.Operations

module _ {ℓ : Level} {ring : Ring {ℓ}} where
  open Ring ring

  infix 1 eval


  eval : (ℕ → R) → Term ring → R
  eval _ (` x) = x                    
  eval f (# n) = f n
  eval f (t `+ t₁) = (eval f t) R+ (eval f t₁)
  eval f (t `* t₁) = (eval f t) R* (eval f t₁)

