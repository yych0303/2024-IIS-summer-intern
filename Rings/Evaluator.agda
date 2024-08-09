{-# OPTIONS --allow-unsolved-metas #-}
module Rings.Evaluator where

open import N-cal

open import Rings.CommutativeRing
open import Rings.RingN
open import Rings.RingLN
open import Rings.RingSt
open import Rings.RingType




   
evalℕ : Term ℕ → ℕ
evalℕ = eval ringℕ

evalListℕ : Term (List ℕ) → List ℕ
evalListℕ = eval ringListℕ


evalSt : {A : Set} → Term (St A) → St A
evalSt {A} = eval (ringSt A)


{-


evalType : Term Type → Type
evalType = eval ringType


-}