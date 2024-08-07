### Interface of commutative ring

## Main frame

```block
  Term R        Term R
    |             |
    |             |
eval ringR    eval ringR
    |             |
    V             V
    A ---- ≃ ---- B

```

```agda
module CommutativeRing where

open import Agda.Primitive
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (Dec)



-- Commutative Ring
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R               : Set ℓ
    R0              : R
    R1              : R
    Rpre            : R → R
    -- Operations -------------
    _R+_            : R → R → R
    _R*_            : R → R → R   
--    RIdx          : Idx → R
    -- Equivalence relation ----
    _≃_             : Rel R ℓ
    isDecEquivR0    : ∀ (x : R) → Dec (R0 ≃ x)
    refl            : ∀ {x : R} → x ≃ x
    trans           : ∀ {x y z : R} → x ≃ y → y ≃ z → x ≃ z
    sym             : ∀ {x y : R} → x ≃ y → y ≃ x

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
## Properties

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



module Properties {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  -- zero-identity+r : ∀ {x : R} → (R0 R+ x) ≃ x
  -- zero-identity+r {x} = {!   !}

``` 