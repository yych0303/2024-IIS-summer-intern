{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.Func where

open import Ring.Data.RingN
open import Ring.Data.RingLN
open import Ring.Data.RingSt
open import Ring.Data.RingType


-- func ------------------------------------------------------------------

funcℕStℕ : ℕ → St ℕ
funcℕStℕ = λ n → map [_] (iterate suc 0 n)

funcℕListℕ : ℕ → List ℕ
funcℕListℕ = [_]ᶜ
    where
      [_]ᶜ : ℕ → List ℕ
      [ n ]ᶜ = iterate suc 0 n
