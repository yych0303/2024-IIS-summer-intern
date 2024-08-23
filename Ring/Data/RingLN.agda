{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.RingLN where

open import Ring.Base

-- Ring (List ℕ) -----------------------------------------------
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- public
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_) public
open import Data.List.Base public

ringListℕ : Ring
ringListℕ = record  
  { R               = List ℕ          
  ; R0              = []        
  ; R1              = [ 0 ]     
  ; _R+_            = r+          
  ; _R*_            = r*                
  ; Rhead           = λ {[] → [] ; (x ∷ _) → [ 0 ]}     
  ; Rtail           = λ {[] → [] ; (_ ∷ xs) → xs}   
  ; _~_             = _≡_  
  ; ~-R0            = λ {[] → true ; _ → false }    
  ; ~-refl          = refl          
  ; ~-trans         = λ x y → trans x y         
  ; ~-sym           = λ x → sym x
  ; Rhead-tail      = ht
  ; Rhead-0h        = {!   !}
  ; Rhead-h0        = {!   !}
  ; Rhead-n0        = {!   !} 
  ; Rtail-01t       = {!   !} 
  ; Rtail-t01       = {!   !}
  ; Rhead-~         = {!   !}  
  ; Rtail-~         = {!   !}   
  ; R+-identityˡ    = {!   !}
  ; R*-identityˡ    = {!   !}
  ; R+-comm         = {!   !}
  ; R*-comm         = {!   !}
  ; R+-assoc        = {!   !}
  ; R*-assoc        = {!   !}
  ; R*-zeroˡ        = {!   !}
  ; R*-distribˡ-+   = {!   !}
  ; R+-axeqˡ        = {!   !}
  ; R*-axeqˡ        = {!   !}
  }
    where
      r0    = []
      r1    = [ 0 ]
      r+    = λ xs ys → (map ((length ys) +_) xs) ++ ys
      r*    = λ xs ys → foldl (λ acc x → (r+ ys acc)) r0 xs
      ht : {!   !}
      ht [] = refl
      ht (x ∷ x₁) = {!   !}


