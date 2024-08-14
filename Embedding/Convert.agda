module Embedding.Convert where

open import Agda.Primitive
open import Ring.Base public

module _ {a b : Level} (rA : Ring {a} ) ( rB : Ring {b}) where
  open Ring

  open import Data.Product
  open import Data.Sum.Base
  open import Ring.Properties
  
  open import Embedding.Base
  open Embedding   



  private
    A : Set a
    A = R rA
    B : Set b
    B = R rB 
    R0A = R0 rA
    R0B = R0 rB
    R1A = R1 rA
    R1B = R1 rB
    RhA = Rhead rA
    RhB = Rhead rB
    RtA = Rtail rA
    RtB = Rtail rB
    
    _~A_ = _~_ rA
    _~B_ = _~_ rB
    _R+A_ = _R+_ rA
    _R+B_ = _R+_ rB
    _R*A_ = _R*_ rA
    _R*B_ = _R*_ rB
 
  
  conv : (Embedding rA rB) → Ring {a} → Ring {a ⊔ b}
  conv embd rA = record
    { R               = Σ[ y ∈ B ] Σ[ x ∈ A ] (EF embd x ~B y) 
    ; R0              = R0B , R0A , E0 embd             
    ; R1              = R1B , R1A , E1 embd    
    ; Rhead           = λ (y , x , p) → RhB y , RhA x , ~-trans rB (Eh embd x) (Rhead-~ rB p)
    ; Rtail           = λ (y , x , p) → RtB y , RtA x , ~-trans rB (Et embd x) (Rtail-~ rB p)
    ; _R+_            = λ (y , x , p) (y' , x' , p') → (y R+B y') , (x R+A x') , ~-trans rB (E+ embd x x') (R+-axeq rB _ _ _ _ p p')           
    ; _R*_            = λ (y , x , p) (y' , x' , p') → (y R*B y') , (x R*A x') , ~-trans rB (E* embd x x') (R*-axeq rB _ _ _ _ p p')
    ; _~_             = λ (y , _ , _) (y' , _ , _) → (y ~B y') -- _~B_           
    ; ~-R0            = λ (y , _ , _) → ~-R0 rB y -- isDecEquivR0 rB    
    
    ; ~-refl          = ~-refl rB          
    ; ~-trans         = ~-trans rB         
    ; ~-sym           = ~-sym rB

    ; Rhead-tail      = λ r → Rhead-tail rB (proj₁ r)
    
    ; Rhead-0h        = λ r → Rhead-0h rB (proj₁ r)
    ; Rhead-h0        = λ r → Rhead-h0 rB (proj₁ r) 
    ; Rhead-n0        = λ r f → Rhead-n0 rB (proj₁ r) f  
    ; Rtail-01t       = λ r → Rtail-01t rB (proj₁ r)
    ; Rtail-t01       = λ r → Rtail-t01 rB (proj₁ r) 
     
    ; Rhead-~          = Rhead-~ rB
    ; Rtail-~          = Rtail-~ rB

    ; R+-identityˡ     = λ r → R+-identityˡ rB (proj₁ r)
    ; R*-identityˡ     = λ r → R*-identityˡ rB (proj₁ r)
    ; R+-comm          = λ r r' → R+-comm  rB (proj₁ r) (proj₁ r')
    ; R*-comm          = λ r r' → R*-comm rB (proj₁ r) (proj₁ r')
    ; R+-assoc         = λ r r' r'' → R+-assoc rB (proj₁ r) (proj₁ r') (proj₁ r'')
    ; R*-assoc         = λ r r' r'' → R*-assoc rB (proj₁ r) (proj₁ r') (proj₁ r'')
    ; R*-distribˡ-+    = λ r r' r'' → R*-distribˡ-+ rB (proj₁ r) (proj₁ r') (proj₁ r'') 
    ; R*-zeroˡ         = λ r → R*-zeroˡ rB (proj₁ r)
    ; R+-axeqˡ         = λ r r' r'' p → R+-axeqˡ rB (proj₁ r) (proj₁ r') (proj₁ r'') p
    ; R*-axeqˡ         = λ r r' r'' p → R*-axeqˡ rB (proj₁ r) (proj₁ r') (proj₁ r'') p
    }
