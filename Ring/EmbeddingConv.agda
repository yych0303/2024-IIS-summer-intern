
module Ring.EmbeddingConv where
{-


ringA ringB : Ring

embedAB : Embedding ringA ringB


-- range of EF
B = Σ A (Embedding.EF embedAB)

funcAB = Embedding.EF embedAB

conv : {rA rB : Ring} →  (Embedding rA rB) → Ring → Ring


[abstract]   
ringA : Ring --- conv embedAB ---> ringEFA : Ring


-}
open import Agda.Primitive
open import Ring.Base


module _ {a b : Level} (rA : Ring {a} ) ( rB : Ring {b}) where
  open Ring


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


  record Embedding : Set (a ⊔ b) where
    field
      -- Homomorphic
      EF : A → B
      E0 : EF (R0 rA) ~B (R0 rB) 
      E1 : EF (R1A) ~B (R1B) 
      Eh : ∀ {x : A} → EF (RhA x) ~B RhB (EF x) 
      Et : ∀ {x : A} → EF (RtA x) ~B RtB (EF x) 
      E+ : ∀ {x y : A} → EF (x R+A y) ~B ((EF x) R+B (EF y)) 
      E* : ∀ {x y : A} → EF (x R*A y) ~B ((EF x) R*B (EF y))

      -- Embedding
      E-~    : ∀ {x y : A} → x ~A y → (EF x) ~B (EF y) 
  open Embedding    



{-
  open import Agda.Builtin.Sigma
    
  conv : (Embedding) → Ring {a} → Ring {b}
  conv embd rA = record
    { R               = {! Σ A (EF embd) !}              
    ; R0              = R0B             
    ; R1              = R1B     
    ; Rhead           = RhB     
    ; Rtail           = RtB        
    ; _R+_            = _R+B_           
    ; _R*_            = _R*B_                  
    ; _~_             = _~B_           
    ; isDecEquivR0    = isDecEquivR0 rB    
    ; refl            = {!   !}          
    ; trans           = {!   !}         
    ; sym             = {!   !}
    ; head-tail       = {!   !}
    ; head-0          = {!   !}
    ; head-n0         = {!   !} 
    ; tail-01         = {!   !} 
    ; zero-identity+  = {!   !}
    ; one-identity*   = {!   !}
    ; comm+           = {!   !}
    ; comm*           = {!   !}
    ; assoc+          = {!   !}
    ; assoc*          = {!   !}
    ; distrib         = {!   !} 
    }
      where


-}
      
-- 
--    
--      
--    reflA = refl rA
--    reflB = refl rB
--    transA = trans rA
--    transB = trans rB
--    symA = sym rA
--    symB = sym rB
--      
--    E-refl : ∀ {x : A} → reflA {x} → reflB {EF x}
--    E-trans  : ∀ {x y z : R} → transA {x} {y} {z} → transB {EF x} {EF y} {EF z}
--    E-sym    : ∀ {x y : R} → symA {x} {y} → symB {EF x} {EF y}
--