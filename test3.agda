open import Ring.EmbeddingConv



open import Ring.Data.RingN
-- open import Ring.Data.RingSt
open import Ring.Data.RingKu



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




open import Term.Base
open import Term.Eval

-- open import Data.Fin.Base
open import Ring.Data.Func

open import Term.Trns





  