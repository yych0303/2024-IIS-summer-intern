open import Term.Base
open import Term.Eval
open import Ring.Data.RingN


-- P 5 3 + 2 * 3
ex1 = `P[ ` 5 , ` 3 ] `+ ` 2 `* ` 3
ex1n = eval ringℕ ex1 -- 66

--  sigma (x ∈ {2, 3, 4}) C x 2 = 10
ex2 = `Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ] 
ex2n = eval ringℕ ex2 -- 10 


open import Ring.Data.RingSt

-- C 5 3 as list of list
ex3 = `C[ ` ([ 4 ] ∷ [ 3 ] ∷ [ 2 ] ∷ [ 1 ] ∷ [ 0 ] ∷ []) , ` ([ 2 ] ∷ [ 1 ] ∷ [ 0 ] ∷ []) ] 
ex3st = eval (ringSt ℕ) ex3

open import Term.Trns
open import Ring.Data.Func -- funcℕStℕ


-- C 5 3 as list of list by translator
ex4 = `C[ ` 5 , ` 3 ] 
ex4st = eval (ringSt ℕ) (trns funcℕStℕ ex4)



-- open import Ring.Data.RingType

-- open import Ring.EmbeddingConv



