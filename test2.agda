open import Ring.EmbeddingConv
open import Ring.Data.RingN
open import Ring.Data.RingSt
open import Ring.Data.RingType

open import Term.Base
open import Term.Eval

-- open import Data.Fin.Base
open import Ring.Data.Func

open import Term.Trns




-- LN
open import Ring.Data.RingLN
open Ring (ringSt ℕ)

pfs :  funcℕStℕ 2 ~ funcℕStℕ 2
pfs = {!   !}

fev = ` (funcℕListℕ 2) `+ ` (funcℕListℕ 4)
fea = ` (funcℕListℕ 4) `* ` (funcℕListℕ 2)
sss = eval ringListℕ fev



St2+4 = ` (funcℕStℕ 2) `+ ` (funcℕStℕ 4)
St4*2 = ` (funcℕStℕ 4) `* ` (funcℕStℕ 2)
StC53 = `C[ ` funcℕStℕ 5 , ` funcℕStℕ 3 ]

ssxs = eval (ringSt ℕ) StC53

open Ring ringType


pf :  funcℕType 2 ~ funcℕType 2
pf = {!   !}

ev = ` (funcℕType 2) `+ ` (funcℕType 4)
ea = ` (funcℕType 4) `+ ` (funcℕType 2)
T = Ring._~_ ringType (eval ringType ev) (eval ringType ea)

r : Ring._~_ ringType (eval ringType ev) (eval ringType ea)

r = record { to = {! [ ? , ? ]  !} ; from = {!   !} ; from∘to = {!   !} ; to∘from = {!   !} }


en = ` (2) `+ ` (4)


embNN : Embedding ringℕ ringℕ
embNN = record
  { EF = λ x → x
  ; E0 = refl
  ; E1 = refl
  ; Eh = refl
  ; Et = refl 
  ; E+ = refl  
  ; E* = refl
  ; E~ = λ p → p
  }

open Embedding
open import Data.Nat

f : ℕ → ℕ
f = {!   !}
postulate
  p : ∀ (u w : ℕ) → f u ≡ w

q : ∀ (u v w : ℕ) → f u ≡ w 
q = λ u v w → E~ embNN (p u w) 



module _ where

  open import Term.TermReasoning 
  open ≈-Reasoning ringℕ
  open import Data.Nat.Properties
  
  ngv = ` (2) `+ ` (4)
  nga = ` (4) `+ ` (2)

  -- nh : ` (2) `+ ` (4) ≈ ` (4) `+ ` (2)
--  nh = 
--    ≈-begin
--      (` (2) `+ ` (4)) 
--    ≈⟨ {! +-comm  !} ⟩ 
--      (` (4) `+ ` (2))  
--    ≈-∎




module _ where

  open import Term.TermReasoning
  open ≈-Reasoning ringType

  gv = ` (funcℕType 2) `+ ` (funcℕType 4)
  ga = ` (funcℕType 4) `+ ` (funcℕType 2)

--  h : gv ≈ ga 
--  h = ≈-begin {! gv !} ≈⟨ {!   !} ⟩ {!ga  !}  ≈-∎













  