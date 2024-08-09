open import Data.Nat

open import Term.Base
open import Term.Eval
open import Term.Translator

open import Ring.Data.RingN
open import Ring.Data.RingLN
open import Ring.Data.RingSt
open import Ring.Data.RingType

open import Ring.Data.Func


-- ev -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
ev = `Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ] 
uu = eval ringListℕ (trns funcℕListℕ ev)

ee = eval ringListℕ (trns funcℕListℕ (` 2 `* ` 3))



er : (x x₁ : ℕ) → ℕ
er = λ n → λ k → eval ringℕ `C[ ` n `+ ` k , ` k ] 

re : (x x₁ : ℕ) → Term ℕ
re = λ n → λ k → `C[ ` n `+ ` k , ` n ]


ers = eval ringℕ `C[ ` 4 , ` 2 ] 

erss = eval ringℕ  (` 2)   