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

data Bool : Set where
 true false : Bool

open import Agda.Primitive
-- open import Agda.Builtin.Equality
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (Dec; ¬_) public
open import Data.Sum using (_⊎_) public


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
    _~_             : R → R → Set
    ~-R0            : ∀ (x : R) → Bool
    ~-refl          : ∀ {x : R} → x ~ x
    ~-trans         : ∀ {x y z : R} → x ~ y → y ~ z → x ~ z
    ~-sym           : ∀ {x y : R} → x ~ y → y ~ x
    
    -- head-tail properties ---------
    Rhead-tail       : ∀ (x : R) → (Rhead x R+ Rtail x) ~ x
    Rhead-0h         : ∀ (x : R) → (x ~ R0) → (Rhead x ~ R0)
    Rhead-h0         : ∀ (x : R) → (Rhead x ~ R0) → (x ~ R0)
    Rhead-n0         : ∀ (x : R) → (¬(x ~ R0)) → (Rhead x ~ R1) 
    Rtail-01t        : ∀ (x : R) → ((x ~ R0) ⊎ (x ~ R1)) → (Rtail x ~ R0)
    Rtail-t01        : ∀ (x : R) → (Rtail x ~ R0) → ((x ~ R0) ⊎ (x ~ R1))

    Rhead-~          : ∀ {x y : R} → (x ~ y) → (Rhead x ~ Rhead y)
    Rtail-~          : ∀ {x y : R} → (x ~ y) → (Rtail x ~ Rtail y)
    
    -- Commutative Ring properties ---------  
    R+-identityˡ     : ∀ (x : R)     → (R0 R+ x) ~ x
    R*-identityˡ     : ∀ (x : R)     → (R1 R* x) ~ x
    R+-comm          : ∀ (x y : R)   → (x R+ y) ~ (y R+ x)
    R*-comm          : ∀ (x y : R)   → (x R* y) ~ (y R* x)
    R+-assoc         : ∀ (x y z : R) → ((x R+ y) R+ z) ~ (x R+ (y R+ z))
    R*-assoc         : ∀ (x y z : R) → ((x R* y) R* z) ~ (x R* (y R* z))
    R*-zeroˡ         : ∀ (x : R)     → (R0 R* x) ~ R0
    R*-distribˡ-+    : ∀ (x y z : R) → (x R* (y R+ z)) ~ ((x R* y) R+ (x R* z))
    
    -- Axioms of equality
    R+-axeqˡ         : ∀ (x y z : R)   → x ~ y → (z R+ x) ~ (z R+ y)
    R*-axeqˡ         : ∀ (x y z : R)   → x ~ y → (z R* x) ~ (z R* y)
  {-

  record
  { R               = ?              
  ; R0              = ?      
  ; R1              = ?     
  ; Rhead           = ?     
  ; Rtail           = ?        
  ; _R+_            = ?           
  ; _R*_            = ?               
  ; _~_             = ?           
  ; ~-R0            = ?    
  ; ~-refl          = ?          
  ; ~-trans         = ?         
  ; ~-sym           = ?
  ; Rhead-tail      = ? 
  ; Rhead-0h        = ? 
  ; Rhead-h0        = ? 
  ; Rhead-n0        = ?  
  ; Rtail-01t       = ? 
  ; Rtail-t01       = ? 
  ; Rhead-~         = ?  
  ; Rtail-~         = ?   
  ; R+-identityˡ    = ?
  ; R*-identityˡ    = ?
  ; R+-comm         = ?
  ; R*-comm         = ?
  ; R+-assoc        = ?
  ; R*-assoc        = ?
  ; R*-zeroˡ        = ?
  ; R*-distribˡ-+   = ?
  ; R+-axeqˡ        = ?
  ; R*-axeqˡ        = ?
  }

  -}