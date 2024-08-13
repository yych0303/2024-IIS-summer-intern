open import Ring.EmbeddingConv
open import Ring.Data.RingN
open import Ring.Data.RingType

open import Term.Base
open import Term.Eval





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

