## N-calculus

# main frame
...

  Term A -- trns funcAB -> Term B
    |                        |
    |                        |
eval ringA               eval ringB
    |                        |
    V                        V
    A ------- funcAB ------> B



data Term (Val : Set ℓ) : Set ℓ
  `_ | $_ | _`+_ | _`*_ | `Σ[_∈_]_ | `Π[_∈_]_ | 
  [_]`! | `P[_,_] | `C[_,_] 

-- Substitution
[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val


# Interface of commuttative ring
record Ring (R : Type) : Type

# Evaluate Term R to R
eval : (ring : Ring {ℓ}) → Term (R ring) → (R ring)

# Translate Term A to Term B
trns : {A B : Set} → (A → B) → Term A → Term B



```agda
module N-cal where

open import Agda.Primitive
open import Data.List.Base public
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)

private
  variable
    ℓ : Level

St : Set → Set
St A = List (List A)



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




-- [:=] ---------------------------------------------------------------------

[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val
[ i := v ] (` x)                    = ` x
[ i := v ] ($ x) with x Data.String.≟ i
...                         | yes _ = ` v 
...                         | no  _ = $ x
[ i := v ] (t `+ t₁)                = [ i := v ] t `+ [ i := v ] t₁
[ i := v ] (t `* t₁)                = [ i := v ] t `* [ i := v ] t₁
[ i := v ] (`Σ[ x ∈ s ] t)          = `Σ[ x ∈ s ] [ i := v ] t
[ i := v ] (`Π[ x ∈ s ] t)          = `Π[ x ∈ s ] [ i := v ] t
[ i := v ] [ t ]`!                  = [ [ i := v ] t ]`!
[ i := v ] `P[ t , t₁ ]             = `P[ [ i := v ] t , [ i := v ] t₁ ]
[ i := v ] `C[ t , t₁ ]             = `C[ [ i := v ] t , [ i := v ] t₁ ]




-- Ring (Set) : Set -------------------------------------------------------
open import Relation.Binary.Core using (Rel)


-- Commutative Ring
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R             : Set ℓ
    R0            : R
    R1            : R
    -- Operations -------------
    _R+_          : R → R → R
    _R*_          : R → R → R   
    RIdx          : Idx → R
    RP            : R → R → R
    RC            : R → R → R 
    -- Equivalence relation ----
    _≃_           : Rel R ℓ
    refl          : ∀ {x : R} 
                    -----
                  → x ≃ x
    trans         : ∀ {x y z : R}
                  → x ≃ y
                  → y ≃ z
                    -----
                  → x ≃ z
    sym           : ∀ {x y : R}
                  → x ≃ y
                    -----
                  → y ≃ x
    -- Ring properties ---------
    R0-identity+  : ∀ {x : R}
                  → (R0 R+ x) ≃ (R0 R+ x)
    R1-identity*  : ∀ {x : R}
                  → (R1 R* x) ≃ (R1 R* x)
    R+-commut     : ∀ {x y : R}
                  → (x R+ y) ≃ (x R+ y)
    R*-commut     : ∀ {x y : R}
                  → (x R* y) ≃ (x R* y)
    R+-assoc      : ∀ {x y z : R}
                  → ((x R+ y) R+ z) ≃ (x R+ (y R+ z))
    R*-assoc      : ∀ {x y z : R}
                  → ((x R* y) R* z) ≃ (x R* (y R* z))
    R*-+distr     : ∀ {x y z : R}
                  → (x R* (y R+ z)) ≃ ((x R* y) R+ (x R* z))
    P-C*!         : ∀ {x y : R}
                  → (RP x y) ≃ (RC x y R* RP y y)
    


open Ring



-- eval : Ring → Term R → R ----------------------

private rsigma : (ring : Ring {ℓ}) → List (R ring) → ((R ring) → (R ring)) → (R ring)
rsigma ring []      F = R0   ring
rsigma ring (i ∷ l) F = _R+_ ring (F i) (rsigma ring l F)

private rpi : (ring : Ring {ℓ}) → List (R ring) → ((R ring) → (R ring)) → (R ring)
rpi ring []      F = R1   ring
rpi ring (i ∷ l) F = _R*_ ring (F i) (rsigma ring l F)

private r! : (ring : Ring {ℓ}) → (R ring) → (R ring)
r! ring r =  RP ring r r 

-- RC : {ℓ ℓ₁ : Level} (ring : EvalOps {ℓ} {ℓ₁}) → R ring → Val ring → R ring
-- RC ring a k = {!  !}

-- private RP : {ℓ ℓ₁ : Level} (ring : EvalOps {ℓ} {ℓ₁}) → R ring → R ring → R ring
-- RP ring R B = R! ring {!   !}


infix 1 eval

{-# NON_TERMINATING #-}
eval : (ring : Ring {ℓ}) → Term (R ring) → (R ring)
eval ring term with term
...     | (` v)            = v
...     | ($ i)            = RIdx    ring i -- not possible
...     | (t `+ t₁)        = _R+_    ring (eval ring t) (eval ring t₁)
...     | (t `* t₁)        = _R*_    ring (eval ring t) (eval ring t₁)
...     | `P[ t , t₁ ]     = RP      ring (eval ring t) (eval ring t₁)
...     | `C[ t , t₁ ]     = RC      ring (eval ring t) (eval ring t₁)
...     | (`Σ[ i ∈ l ] t)  = rsigma  ring l (λ v → eval ring ([ i := v ] t))
...     | (`Π[ i ∈ l ] t)  = rpi     ring l (λ v → eval ring ([ i := v ] t))
...     | [ t ]`!          = r!      ring (eval ring t)


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

-- Reasoning -------------------------------------------------------------



















{-

OrdRing : (R : Set ℓ₁) 
        → (R0 : R) 
        → (RS : R → R) 
        → (R+ : R → R → R)
        → (R* : R → R → R)
        ------------------
        → Ring R
OrdRing r r0 rs r+ r* = record
  { R0   = r0
  ; R1   = r1
  ; _R+_ = r+
  ; _R*_ = r*
  ; RP   = rP
  ; RC   = rC
  }
    where
      r1 = rs r0
        
      rP : R → R → R
      rP _  0 = r1
      rP [] _ = r0
      rP (x ∷ xs) (suc k) = r* (x ∷ xs) (rP xs k)
      
      rC : R → R → R
      rC _ 0 = r1
      rC [] _ = r0
      rC (rs rn) (rs rk) = rC xs (suc j) ++ rC xs j



-}







```    