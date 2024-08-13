{-# OPTIONS --allow-unsolved-metas #-}
module Term.Eval where

-- Evaluate Term R to R
-- eval : Ring → Term R → R ----------------------

open import Agda.Primitive
open import Relation.Nullary using (yes; no)

open import Term.Base
open import Ring.Base


module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  private 
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

  infix 1 eval

  {-# NON_TERMINATING #-}
  eval : Term R → R
  eval term with term
  ...          | (` v)            = v
  ...          | ($ i)            = R0   -- not possible
  ...          | (t `+ t₁)        = (eval t) R+ (eval t₁)
  ...          | (t `* t₁)        = (eval t) R* (eval t₁)
  ...          | `P[ t , t₁ ]     = rP (eval t) (eval t₁)
  ...          | `C[ t , t₁ ]     = rC (eval t) (eval t₁)
  ...          | (`Σ[ i ∈ l ] t)  = rsigma l (λ v → eval ([ i := v ] t))
  ...          | (`Π[ i ∈ l ] t)  = rpi l (λ v → eval ([ i := v ] t))
  ...          | [ t ]`!          = r! (eval t)