module FinSet.Base where

open import Agda.Primitive
open import Data.Nat.Base
open import FinSet.Membership public


record FinSet {i : Level} : Set (lsuc i) where
  field
    Carrier : Set i
    list : List Carrier
    enum : Enum list  -- (aₑ : Carrier) → aₑ ∈ list
    once : Once list    -- (a₁ : Carrier) → a₁ ∈ list → a₁ ∈₁ list
open FinSet public
                    