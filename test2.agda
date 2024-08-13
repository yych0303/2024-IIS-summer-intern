open import Ring.EmbeddingConv
open import Ring.Data.RingN
open import Ring.Data.RingSt
open import Ring.Data.RingType

open import Term.Base
open import Term.Eval

open import Data.Fin.Base
open import Ring.Data.Func

open import Term.Trns

variable
  X Y : Set



-- LN
open import Ring.Data.RingLN

fev = ` (funcℕListℕ 2) `+ ` (funcℕListℕ 4)
fea = ` (funcℕListℕ 4) `* ` (funcℕListℕ 2)
sss = eval ringListℕ fev



St2+4 = ` (funcℕStℕ 2) `+ ` (funcℕStℕ 4)
St4*2 = ` (funcℕStℕ 4) `* ` (funcℕStℕ 2)
StC53 = `C[ ` funcℕStℕ 5 , ` funcℕStℕ 3 ]

ssxs = eval (ringSt ℕ) StC53



ev = ` (funcℕType 2) `+ ` (funcℕType 4)
ea = ` (funcℕType 4) `+ ` (funcℕType 2)
T = Ring._~_ ringType (eval ringType ev) (eval ringType ea)

r : Ring._~_ ringType (eval ringType ev) (eval ringType ea)

r = {!   !}


en = ` (2) `+ ` (4)


embNN : Embedding ringℕ ringℕ
embNN = record
  { EF = λ x → x
  ; E0 = {!   !}
  ; E1 = {!   !}
  ; Eh = {!   !}
  ; Et = {!   !} 
  ; E+ = {!   !}  
  ; E* = {!   !}
  ; E~ = {!   !}
  }

open import Term.TermReasoning

open RS ringType

gv = ` (funcℕType 2) `+ ` (funcℕType 4)
ga = ` (funcℕType 4) `+ ` (funcℕType 2)

h : gv ≈ ga 
h = {!   !}










 