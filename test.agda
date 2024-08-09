open import Data.Nat

open import Terms.N-cal
open import Terms.Eval
open import Terms.Translator

open import Rings.Data.RingN
open import Rings.Data.RingLN
open import Rings.Data.RingSt
open import Rings.Data.RingType

open import Rings.Func


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