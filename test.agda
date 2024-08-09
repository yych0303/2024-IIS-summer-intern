open import N-cal
open import Rings.RingN
open import Rings.RingLN
open import Rings.RingSt
open import Rings.RingType

open import Translator
open import Func

open import Data.Nat

-- ev -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
ev = `Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ] 
uu = evalListℕ (trns funcℕListℕ ev)

ee = evalListℕ (trns funcℕListℕ (` 2 `* ` 3))



er : (x x₁ : ℕ) → ℕ
er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 

re : (x x₁ : ℕ) → Term ℕ
re = λ n → λ k → `C[ ` n `+ ` k , ` n ]


ers = evalℕ `C[ ` 4 , ` 2 ] 

erss = evalℕ  (` 2)   