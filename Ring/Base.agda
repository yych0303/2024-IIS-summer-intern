module Ring.Base where

{-
  Term R        Term R
    |             |
    |             |
eval ringR    eval ringR
    |             |
    V             V
    r ---- ~ ---- r'

-}


open import Agda.Primitive
-- open import Agda.Builtin.Equality
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (Dec; ¬_) public
open import Data.Sum using (_⊎_) public
open import Data.Empty public

record _↔_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  field
    to      : A → B
    from    : B → A


-- Commutative Ring
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R               : Set ℓ
    R0              : R
    R1              : R
    Rhead            : R → R
    Rtail            : R → R
    -- Operations -------------
    _R+_            : R → R → R
    _R*_            : R → R → R   
--    RIdx          : Idx → R
    -- Equivalence relation ----
    _~_             : Rel R ℓ
    isDecEquivR0    : ∀ (x : R) → Dec (R0 ~ x)
    refl            : ∀ {x : R} → x ~ x
    trans           : ∀ {x y z : R} → x ~ y → y ~ z → x ~ z
    sym             : ∀ {x y : R} → x ~ y → y ~ x

    -- head-tail properties ---------
    head-tail       : ∀ (x : R) → (Rhead x R+ Rtail x) ~ x
    head-0          : ∀ (x : R) → (x ~ R0) ↔ (Rhead x ~ R0)
    head-n0         : ∀ (x : R) → (¬(x ~ R0)) → (Rhead x ~ R1) 
    tail-01         : ∀ (x : R) → ((x ~ R0) ⊎ (x ~ R1)) ↔ (Rtail x ~ R0)
    -- Commutative Ring properties ---------  
    zero-identity+  : ∀ (x : R)     → (R0 R+ x) ~ x
    one-identity*   : ∀ (x : R)     → (R1 R* x) ~ x
    comm+           : ∀ (x y : R)   → (x R+ y) ~ (y R+ x)
    comm*           : ∀ (x y : R)   → (x R* y) ~ (y R* x)
    assoc+          : ∀ (x y z : R) → ((x R+ y) R+ z) ~ (x R+ (y R+ z))
    assoc*          : ∀ (x y z : R) → ((x R* y) R* z) ~ (x R* (y R* z))
    distrib         : ∀ (x y z : R) → (x R* (y R+ z)) ~ ((x R* y) R+ (x R* z))


  {-

  record
  { R               = ?              
  ; R0              = r0             
  ; R1              = r1     
  ; Rhead           = ?     
  ; Rtail           = ?        
  ; _R+_            = _r+_           
  ; _R*_            = _r*_               
  ; _~_             = ?           
  ; isDecEquivR0    = ?    
  ; refl            = ?          
  ; trans           = ?         
  ; sym             = ?
  ; head-tail       = ?
  ; head-0          = ?
  ; head-n0         = ? 
  ; tail-01         = ? 
  ; zero-identity+  = ?
  ; one-identity*   = ?
  ; comm+           = ?
  ; comm*           = ?
  ; assoc+          = ?
  ; assoc*          = ?
  ; distrib         = ? 
  }
    where
      r0   = ?
      r1   = ?
      _r+_ = ?
      _r*_ = ?    


  -}