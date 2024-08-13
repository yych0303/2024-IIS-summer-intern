{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.RingSt where

open import Ring.Base

-- Ring (St A) ---------------------------------------------------- 
open import Relation.Nullary using (yes; no)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.List


-- public
open import Data.List.Base public

St : Set → Set
St A = List (List A)

{-
private
  variable
    A : Set

infix 0 _≅_
record _≅_ (x y : St A) : Set where
  field
    to   : List A → List A
    from : List A → List A
    from∘to : 
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≅_
-}


ringSt : Set → Ring
ringSt A = record
  { R               = St A
  ; R0              = r0
  ; R1              = r1  
  ; Rhead           = rh     
  ; Rtail           = rt   
  ; _R+_            = r+
  ; _R*_            = r*
  ; _~_             = λ x y → length x ≡ length y             
  ; ~-R0            = λ { [] → true ; _ → false }  
  ; ~-refl          = {!   !}          
  ; ~-trans         = {!   !}         
  ; ~-sym           = {!   !}
  ; Rhead-tail      = {!   !}
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

      dec : (x : List (List A)) → Dec (zero ≡ foldr (λ _ → suc) zero x)
      dec x = {!   !}  
