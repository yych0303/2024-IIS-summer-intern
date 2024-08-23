module Embedding.Base where

open import Agda.Primitive
open import Ring.Base public


module _ {a b : Level} (rA : Ring {a} ) ( rB : Ring {b}) where
  open Ring

  open import Data.Product
  open import Data.Sum.Base
  -- open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
  open import Ring.Properties
    

  record Embedding : Set (a ⊔ b) where
    field
      -- Homomorphic
      EF : R rA → R rB
      E0 : _~_ rB (EF (R0 rA)) (R0 rB) 
      E1 : _~_ rB (EF (R1 rA)) (R1 rB) 
      E+ : ∀ (x y : R rA) → _~_ rB (EF (_R+_ rA x y)) (_R+_ rB (EF x) (EF y)) 
      E* : ∀ (x y : R rA) → _~_ rB (EF (_R*_ rA x y)) (_R*_ rB (EF x) (EF y))
      Eh : ∀ (x : R rA) → _~_ rB (EF (Rhead rA x)) (Rhead rB (EF x)) 
      Et : ∀ (x : R rA) → _~_ rB (EF (Rtail rA x)) (Rtail rB (EF x)) 

      -- Embedding
      E~ : ∀ (x y : R rA) → _~_ rA x y → _~_ rB (EF x) (EF y) 
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

{-
open import Ring.Data.RingN
   

embNN : Embedding ringℕ ringℕ
embNN = record
  { EF = λ x → x
  ; E0 = {!   !}
  ; E1 = {!   !}
  ; Eh = {!   !}
  ; Et = {!   !} 
  ; E+ = {!   !}  
  ; E* = {!   !}
  ; E~ = ?
  }

-}