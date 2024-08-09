{-# OPTIONS --allow-unsolved-metas #-}
module Rings.RingSt where

open import Rings.CommutativeRing
-- Ring (St A) ---------------------------------------------------- 
open import Relation.Nullary using (yes; no)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
-- public
open import Data.List.Base public

St : Set → Set
St A = List (List A)

ringSt : Set → Ring
ringSt A = record
  { R               = St A
  ; R0              = r0
  ; R1              = r1  
  ; Rhead           = rh     
  ; Rtail           = rt   
  ; _R+_            = r+
  ; _R*_            = r*
  ; _≃_             = λ x y → length x ≡ length y    
  ; isDecEquivR0    = λ x → 0 ≟ length x
  ; refl            = refl          
  ; trans           = λ x y → trans x y         
  ; sym             = λ x → sym x  
  ; head-tail       = λ x → cong length (ht x)
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
      r0 : {A : Set} → St A
      r0 = []
      r1 : {A : Set} → St A
      r1 = [ [] ]
      rh : (List (List A)) → List (List A)
      rh [] = []
      rh (x ∷ _) = [ x ]
      rt : (List (List A)) → List (List A)
      rt [] = []
      rt (_ ∷ xs) = xs

      r+ : {A : Set} → St A → St A → St A
      r+ = _++_
      r* : {A : Set} → St A → St A → St A
      r* = λ xs ys → concatMap (λ x → map (x ++_) ys ) xs

      ht : (x : List (List A)) → r+ (rh x) (rt x) ≡ x
      ht [] = refl
      ht (x ∷ x₁) = refl
