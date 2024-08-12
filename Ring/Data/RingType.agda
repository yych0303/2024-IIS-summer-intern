{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.RingType where

open import Ring.Base
-- Ring Type ---------------------------------------------------- 

-- Type = Set

open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ) renaming (suc to fsuc ; zero to fzero)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

open import Data.Nat
open import Data.Product
open import Agda.Primitive

infix 0 _≃_
record _≃_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_


ringType : Ring
ringType = record 
  { R               = {u : Level} → Σ[ X ∈ Set u ] Σ[ n ∈ ℕ ] (Fin n ≃ X)         
  ; R0              = (Fin 0) , (zero , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl })             
  ; R1              = (Fin 1) , (1 , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl }) --r1     
  ; Rhead           = {!   !} -- rh     
  ; Rtail           = {!   !} --rt        
  ; _R+_            = {!   !}         
  ; _R*_            = {!   !}             
  ; _~_             = {! λ X Y → proj₁ X ≃ proj₁ Y !}           
  ; isDecEquivR0    = {!   !}    
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
      r0    = Fin 0
      r1    = Fin 1
      _r+_ = _⊎_
      _r*_ = _×_
      rh   = {!   !}
      rt   = {!   !}




c : Σ[ X ∈ Set ] Σ[ n ∈ ℕ ] (Fin n ≃ X)
c = Fin 4 , (4 , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl })

d : Σ[ x ∈ ℕ ] Fin x
d = {!   !} , {!   !}      
