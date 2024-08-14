open import Embedding.Base


open import Relation.Binary.PropositionalEquality.Core using (cong₂)
open import Ring.Data.RingN
-- open import Ring.Data.RingSt
open import Ring.Data.RingKu

open import Data.List.Properties

open FinSet

embNN : Embedding ringType ringℕ
embNN = record
  { EF = λ x → length (list x)                                       
  ; E0 = refl                                       
  ; E1 = refl                                       
  ; Eh = {!   !}                                       
  ; Et = {!   !}                                        
  ; E+ = λ x y → trans (length-++ (map inj₁ (list x)) {map inj₂ (list y)}) (cong₂ _+_ (length-map inj₁ (list x)) (length-map inj₂ (list y)))                              
  ; E* = {!   !}                                       
  ; E~ = λ p → {!   !}                                       
  }






  