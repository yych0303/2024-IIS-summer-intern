open import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat
open import Data.Nat.Properties

open ≤-Reasoning
-- Define the example function
example : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
example {a} {b} {c} a≤b b≤c = begin
  a ≤⟨ a≤b ⟩
  b ≤⟨ b≤c ⟩
  c ∎
