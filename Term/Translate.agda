module Term.Translate where
-- Translate Term A to Term B

open import Agda.Primitive

open import Term.Base
open import Embedding.Base

-- trns : (R → B) → Term R → Term B-----------------------------------------------------------------

open import Ring.Base

module _ {a b : Level} {rA : Ring {a}} {rB : Ring {b}} (emb : Embedding rA rB) where
  open Embedding emb
  open Ring
  private
    A = R rA
    B = R rB
  
  infix 1 trns

  trns : Term rA → Term rB
  trns (` x) = ` (EF x)
--  trns (& n) = {! ` (EF x)  !}
  trns (t `+ t₁) = trns t `+ trns t₁
  trns (t `* t₁) = trns t `* trns t₁


  evtr : Term rA → B
  evtr (` x) = EF x  
--  evtr (& x) = {!   !}                   
  evtr (t `+ t₁) = _R+_ rB (evtr t) (evtr t₁)   
  evtr (t `* t₁) = _R*_ rB (evtr  t) (evtr t₁)  


