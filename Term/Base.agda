module Term.Base where
    
open import Agda.Primitive
open import Data.List.Base public
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)

open import Data.Nat.Base

-- Term --------------------------------------------------------------

private Idx : Set
Idx = String

open import Ring.Base

module _  {ℓ : Level} (ring : Ring {ℓ} ) where
  open Ring ring

--  infix  5 `Σ[_∈_]_ `Π[_∈_]_ 
--  infixl 6 `C[_,_]  `P[_,_]
  infixl 7  _`+_
  infixl 8  _`*_
--  infixl 9  [_]`!
--  infix  9  $_
  infix 9  `_ 
--  infix 9 #_

  data Term : Set ℓ where
    `_          : R → Term
    #_          : ℕ → Term
    _`+_        : Term → Term → Term
    _`*_        : Term → Term → Term
--    $_          : Idx → Term
--    `Σ[_∈_]_    : Idx → List R → Term → Term
--    `Π[_∈_]_    : Idx → List R → Term → Term
--    [_]`!       : Term → Term
--    `P[_,_]     : Term → Term → Term
--    `C[_,_]     : Term → Term → Term

  -- Substitution

  -- [:=] ---------------------------------------------------------------------

--
--module _  {ℓ : Level} {ring : Ring {ℓ} } where
--  open Ring ring
--
--  infix  9  [_:=_]_
--
--  [_:=_]_ : Idx → R → Term ring → Term ring
--  [ i := v ] (` x)            = ` x
----  [ i := v ] ($ x) with x ≟ i
----  ...                 | yes _ = ` v 
----  ...                 | no  _ = $ x
--  [ i := v ] (t `+ t₁)        = [ i := v ] t `+ [ i := v ] t₁
--  [ i := v ] (t `* t₁)        = [ i := v ] t `* [ i := v ] t₁
----  [ i := v ] (`Σ[ x ∈ s ] t)  = `Σ[ x ∈ s ] [ i := v ] t
----  [ i := v ] (`Π[ x ∈ s ] t)  = `Π[ x ∈ s ] [ i := v ] t
----  [ i := v ] [ t ]`!          = [ [ i := v ] t ]`!
----  [ i := v ] `P[ t , t₁ ]     = `P[ [ i := v ] t , [ i := v ] t₁ ]
----  [ i := v ] `C[ t , t₁ ]     = `C[ [ i := v ] t , [ i := v ] t₁ ]
--
--