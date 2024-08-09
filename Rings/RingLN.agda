{-# OPTIONS --allow-unsolved-metas #-}
module Rings.RingLN where

open import Rings.CommutativeRing
-- Ring (List ℕ) -----------------------------------------------
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
-- open import Data.Nat.Properties
-- public
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_) public
open import Data.List.Base public

ringListℕ : Ring
ringListℕ = record  
  { R               = List ℕ          
  ; R0              = []        
  ; R1              = [ 0 ]     
  ; Rhead           = λ {[] → [] ; (x ∷ _) → [ 0 ]}     
  ; Rtail           = λ {[] → [] ; (_ ∷ xs) → xs}   
  ; _R+_            = r+          
  ; _R*_            = r*                
  ; _≃_             = _≡_    
  ; isDecEquivR0    = λ {[] → yes refl ; (x ∷ xs) → no λ ()}
  ; refl            = refl          
  ; trans           = λ x y → trans x y         
  ; sym             = λ x → sym x
  ; head-tail       = ht
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
      r0    = []
      r1    = [ 0 ]
      r+    = λ xs ys → (map ((length ys) +_) xs) ++ ys
      r*    = λ xs ys → foldl (λ acc x → (r+ ys acc)) r0 xs
      ht : {!   !}
      ht [] = refl
      ht (x ∷ x₁) = {!   !}


