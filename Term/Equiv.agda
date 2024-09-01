module Term.Equiv where

open import Ring.Base
open import Term.Base
open import Term.Evaluate

open import Agda.Primitive



module _ {ℓ : Level} {ring : Ring {ℓ}} where
  open Ring ring
  
  infix 0 _≈_
  
  _≈_ : Term ring → Term ring → Set _
  t ≈ t' = (eval t) ~ (eval t')
