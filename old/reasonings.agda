module _ where  
  open import Data.Nat
  open import Data.Nat.Properties
  open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

  example : ∀ (a b c : ℕ) → a ≤ b → b ≤ c → a ≤ c
  example a b c a≤b b≤c = 
    ≤-begin
      a 
    ≤⟨ a≤b ⟩
      b 
    ≤⟨ b≤c ⟩
      c 
    ≤-∎

  EFF : ∀ (n : ℕ) → n ≡ n
  EFF zero = refl
  EFF (suc n) =  
    ≡-begin
      suc n 
    ≡⟨ refl ⟩
      suc n
    ≡-∎
