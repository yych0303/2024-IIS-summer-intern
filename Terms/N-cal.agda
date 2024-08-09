module Terms.N-cal where

{-
-- N-calculus Interface of ring
```block

  Term R 
    |       
    |       
eval ringR
    |       
    V                 
    A 
-}
  
open import Agda.Primitive
open import Data.List.Base public
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)

open import Rings.CommutativeRing public


-- Term --------------------------------------------------------------

infix  5 `Σ[_∈_]_ `Π[_∈_]_ 
infixl 6 `C[_,_]  `P[_,_]
infixl 7  _`*_
infixl 7  _`+_
infix  9  [_:=_]_
infixl 9  [_]`!
infix  9  `_ $_

private Idx : Set
Idx = String

data Term {ℓ : Level} (Val : Set ℓ) : Set ℓ where
  `_          : Val → Term Val
  $_          : Idx → Term Val
  _`+_        : Term Val → Term Val → Term Val
  _`*_        : Term Val → Term Val → Term Val
  `Σ[_∈_]_    : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_    : Idx → List Val → Term Val → Term Val
  [_]`!       : Term Val → Term Val
  `P[_,_]     : Term Val → Term Val → Term Val
  `C[_,_]     : Term Val → Term Val → Term Val

-- Substitution

-- [:=] ---------------------------------------------------------------------

[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val
[ i := v ] (` x)            = ` x
[ i := v ] ($ x) with x ≟ i
...                 | yes _ = ` v 
...                 | no  _ = $ x
[ i := v ] (t `+ t₁)        = [ i := v ] t `+ [ i := v ] t₁
[ i := v ] (t `* t₁)        = [ i := v ] t `* [ i := v ] t₁
[ i := v ] (`Σ[ x ∈ s ] t)  = `Σ[ x ∈ s ] [ i := v ] t
[ i := v ] (`Π[ x ∈ s ] t)  = `Π[ x ∈ s ] [ i := v ] t
[ i := v ] [ t ]`!          = [ [ i := v ] t ]`!
[ i := v ] `P[ t , t₁ ]     = `P[ [ i := v ] t , [ i := v ] t₁ ]
[ i := v ] `C[ t , t₁ ]     = `C[ [ i := v ] t , [ i := v ] t₁ ]



-- Evaluate Term R to R
-- eval : Ring → Term R → R ----------------------

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
    rC x y with isDecEquivR0 x | isDecEquivR0 y
    ...                 | _     | yes _ = R1
    ...                 | yes _ | _     = R0 
    ...                 | _     | _     = (Rhead x R* (rC (Rtail x) (Rtail y))) R+ (rC (Rtail x) (y))

    rP : R → R → R
    {-# NON_TERMINATING #-}
    rP x y with isDecEquivR0 x | isDecEquivR0 y
    ...                 | _     | yes _ = R1
    ...                 | yes _ | _     = R0 
    ...                 | _     | _     = x R* (rP (Rtail x) (Rtail y))

    r! : R → R
    r! r =  rP r r 

  infix 1 eval

  {-# NON_TERMINATING #-}
  eval : Term R → R
  eval term with term
  ...          | (` v)            = v
  ...          | ($ i)            = R0   -- not possible
  ...          | (t `+ t₁)        = (eval t) R+ (eval t₁)
  ...          | (t `* t₁)        = (eval t) R+ (eval t₁)
  ...          | `P[ t , t₁ ]     = rP (eval t) (eval t₁)
  ...          | `C[ t , t₁ ]     = rC (eval t) (eval t₁)
  ...          | (`Σ[ i ∈ l ] t)  = rsigma l (λ v → eval ([ i := v ] t))
  ...          | (`Π[ i ∈ l ] t)  = rpi l (λ v → eval ([ i := v ] t))
  ...          | [ t ]`!          = r! (eval t)