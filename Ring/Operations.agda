module Ring.Operations where

open import Level
open import Ring.Base
open import Data.List

module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  rsigma : List R → (R → R) → R
  rsigma []      F = R0  
  rsigma (i ∷ l) F = (F i) R+ (rsigma l F)

  rpi : List R → (R → R) → R
  rpi []      F = R1  
  rpi (i ∷ l) F = (F i) R* (rsigma l F)

  rC : R → R → R
  {-# NON_TERMINATING #-}
  rC x y with ~-R0 x | ~-R0 y
  ...       | _      | true  = R1
  ...       | true   | _     = R0 
  ...       | _      | _     = (Rhead x R* (rC (Rtail x) (Rtail y))) R+ (rC (Rtail x) (y))

  rP : R → R → R
  {-# NON_TERMINATING #-}
  rP x y with ~-R0 x | ~-R0 y
  ...       | _      | true  = R1
  ...       | true   | _     = R0 
  ...       | _      | _     = x R* (rP (Rtail x) (Rtail y))

  r! : R → R
  r! r =  rP r r 

