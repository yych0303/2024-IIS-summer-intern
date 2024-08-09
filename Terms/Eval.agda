{-# OPTIONS --allow-unsolved-metas #-}
module Terms.Eval where

open import Terms.N-cal

open import Rings.CommutativeRing
open import Rings.Data.RingN
open import Rings.Data.RingLN
open import Rings.Data.RingSt
open import Rings.Data.RingType




   
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