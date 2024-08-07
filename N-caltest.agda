open import N-cal
open import Rings

-- ev -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
ev = `Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ] 
uu = evalListℕ (trns funcℕListℕ ev)

_ = evalListℕ (trns funcℕListℕ (` 2 `* ` 3))

er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 
_ = λ n → λ k → `C[ ` n `+ ` k , ` n ]
