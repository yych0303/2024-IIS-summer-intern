# N-calculus

## Main frame

```block
  Term A -- trns funcAB -> Term B
    |                        |
    |                        |
eval ringA               eval ringB
    |                        |
    V                        V
    A ------- funcAB ------> B

```

```agda
module N-cal where

open import Agda.Primitive
open import Data.List.Base public
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no; Dec)

private
  variable
    ℓ ℓ₁ : Level

St : Set → Set
St A = List (List A)

```

## Term

```agda

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

data Term (Val : Set ℓ) : Set ℓ where
  `_          : Val → Term Val
  $_          : Idx → Term Val
  _`+_        : Term Val → Term Val → Term Val
  _`*_        : Term Val → Term Val → Term Val
  `Σ[_∈_]_    : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_    : Idx → List Val → Term Val → Term Val
  [_]`!       : Term Val → Term Val
  `P[_,_]     : Term Val → Term Val → Term Val
  `C[_,_]     : Term Val → Term Val → Term Val


```

### Substitution

```agda


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

```

## Interface of commuttative ring

```agda


-- Ring (Set) : Set -------------------------------------------------------
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)



-- Commutative Ring
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R             : Set ℓ
    R0            : R
    R1            : R
    Rpre          : R → R
    -- Operations -------------
    _R+_          : R → R → R
    _R*_          : R → R → R   
    RIdx          : Idx → R
    -- Equivalence relation ----
    _≃_         : Rel R ℓ
    isDecEquiv  : Decidable (_≃_)
    refl        : ∀ {x : R} → x ≃ x
    trans       : ∀ {x y z : R} → x ≃ y → y ≃ z → x ≃ z
    sym         : ∀ {x y : R} → x ≃ y → y ≃ x

    -- Commutative Ring properties ---------
    zero-pre-one    : R0 ≃ Rpre R1
    zero-identity+  : ∀ {x : R}     → (R0 R+ x) ≃ x
    one-identity*   : ∀ {x : R}     → (R1 R* x) ≃ x
    comm+           : ∀ {x y : R}   → (x R+ y) ≃ (y R+ x)
    comm*           : ∀ {x y : R}   → (x R* y) ≃ (y R* x)
    assoc+          : ∀ {x y z : R} → ((x R+ y) R+ z) ≃ (x R+ (y R+ z))
    assoc*          : ∀ {x y z : R} → ((x R* y) R* z) ≃ (x R* (y R* z))
    distrib         : ∀ {x y z : R} → (x R* (y R+ z)) ≃ ((x R* y) R+ (x R* z))





```

## Evaluate Term R to R

```agda
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
    rC x y with isDecEquiv R0 x | isDecEquiv R0 y
    ...                                 | _     | yes _ = R1
    ...                                 | yes _ | _     = R0 
    ...                                 | _     | _     = (x R* (rC (Rpre x) (Rpre y))) R+ (rC (Rpre x) (y))

    rP : R → R → R
    {-# NON_TERMINATING #-}
    rP x y with isDecEquiv R0 x | isDecEquiv R0 y
    ...                                 | _     | yes _ = R1
    ...                                 | yes _ | _     = R0 
    ...                                 | _     | _     = x R* (rP (Rpre x) (Rpre y))

    r! : R → R
    r! r =  rP r r 

  infix 1 eval

  {-# NON_TERMINATING #-}
  eval : Term R → R
  eval term with term
  ...          | (` v)            = v
  ...          | ($ i)            = RIdx    i -- not possible
  ...          | (t `+ t₁)        = (eval t) R+ (eval t₁)
  ...          | (t `* t₁)        = (eval t) R+ (eval t₁)
  ...          | `P[ t , t₁ ]     = rP (eval t) (eval t₁)
  ...          | `C[ t , t₁ ]     = rC (eval t) (eval t₁)
  ...          | (`Σ[ i ∈ l ] t)  = rsigma l (λ v → eval ([ i := v ] t))
  ...          | (`Π[ i ∈ l ] t)  = rpi l (λ v → eval ([ i := v ] t))
  ...          | [ t ]`!          = r! (eval t)

```

## Translate Term A to Term B

```agda

-- trns : (R → B) → Term R → Term B-----------------------------------------------------------------

infix 1 trns

{-# NON_TERMINATING #-}
trns : {A B : Set} → (A → B) → Term A → Term B
trns func term with term
...     | (` v)            = (` (func v))        
...     | ($ i)            = ($ i)        
...     | (t `+ t₁)        = (trns func t `+ trns func t₁)    
...     | (t `* t₁)        = (trns func t `* trns func t₁)    
...     | `P[ t , t₁ ]     = `P[ trns func t , trns func t₁ ]   
...     | `C[ t , t₁ ]     = `C[ trns func t , trns func t₁ ]   
...     | (`Σ[ i ∈ l ] t)  = (`Σ[ i ∈ map func l ] trns func t)
...     | (`Π[ i ∈ l ] t)  = (`Π[ i ∈ map func l ] trns func t)
...     | [ t ]`!          = [ trns func t ]`!      




```

## Reasoning

```agda

-- Reasoning -------------------------------------------------------------
--    -- Ring properties ---------
--    zero-pre-one    : R0 ≃ Rpre R1
--    zero-identity+  : ∀ {x : R}     → (R0 R+ x) ≃ x
--    one-identity*   : ∀ {x : R}     → (R1 R* x) ≃ x
--    comm+           : ∀ {x y : R}   → (x R+ y) ≃ (y R+ x)
--    comm*           : ∀ {x y : R}   → (x R* y) ≃ (y R* x)
--    assoc+          : ∀ {x y z : R} → ((x R+ y) R+ z) ≃ (x R+ (y R+ z))
--    assoc*          : ∀ {x y z : R} → ((x R* y) R* z) ≃ (x R* (y R* z))
--    distrib         : ∀ {x y z : R} → (x R* (y R+ z)) ≃ ((x R* y) R+ (x R* z))



module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  -- zero-identity+r : ∀ {x : R} → (R0 R+ x) ≃ x
  -- zero-identity+r {x} = {!   !}


```
     