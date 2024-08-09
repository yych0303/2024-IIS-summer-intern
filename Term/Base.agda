module Term.Base where

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

