open import Ring.EmbeddingConv



open import Ring.Data.RingN
-- open import Ring.Data.RingSt
open import Ring.Data.RingKu

open FinSet

embNN : Embedding ringType ringℕ
embNN = record
  { EF = λ x → length (list x)                                       
  ; E0 = refl                                       
  ; E1 = refl                                       
  ; Eh = {!   !}                                       
  ; Et = {!   !}                                        
  ; E+ = {!   !}                                         
  ; E* = {!   !}                                       
  ; E~ = λ p → {!   !}                                       
  }




open import Term.Base
open import Term.Eval

-- open import Data.Fin.Base
open import Ring.Data.Func

open import Term.Trns





  