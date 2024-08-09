{-# OPTIONS --allow-unsolved-metas #-}
module Rings.Func where

open import Rings.CommutativeRing
open import Rings.Data.RingN
open import Rings.Data.RingLN
open import Rings.Data.RingSt
open import Rings.Data.RingType


-- func ------------------------------------------------------------------

funcℕStℕ : ℕ → St ℕ
funcℕStℕ = λ n → map [_] (iterate suc 0 n)

funcℕListℕ : ℕ → List ℕ
funcℕListℕ = [_]ᶜ
    where
      [_]ᶜ : ℕ → List ℕ
      [ n ]ᶜ = iterate suc 0 n
