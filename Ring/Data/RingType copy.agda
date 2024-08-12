{-# OPTIONS --allow-unsolved-metas #-}
-- module Ring.Data.RingType where

open import Ring.Base 
-- Ring Type ---------------------------------------------------- 


open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ) renaming (suc to fsuc ; zero to fzero)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc)
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
  { R               = Σ[ X ∈ Set ] Σ[ n ∈ ℕ ] (Fin n ≃ X)         
  ; R0              = (Fin 0) , (zero , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl })             
  ; R1              = (Fin 1) , (1 , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl }) --r1     
  ; Rhead           = rh
  ; Rtail           = {!   !} --rt        
  ; _R+_            = {!   !}         
  ; _R*_            = {!   !}             
  ; _~_             = λ rX rY → proj₁ rX ≃ proj₁ rY           
  ; ~-R0            = {!   !}    
  ; ~-refl          = {!   !}          
  ; ~-trans         = {!   !}         
  ; ~-sym           = {!   !}
  ; Rhead-tail      = {!   !}
  ; Rhead-0         = {!   !}
  ; Rhead-n0        = {!   !} 
  ; Rtail-01        = {!   !}
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
      r0    = Fin 0
      r1    = Fin 1
      _r+_ = _⊎_
      _r*_ = _×_
      rh : (x : Σ Set (λ z → Σ ℕ (λ z₁ → Fin z₁ ≃ z))) → Σ Set (λ z → Σ ℕ (λ z₁ → Fin z₁ ≃ z))
      rh (X , zero , p)  = (X , zero , p)
      rh (X , suc n , p) = (Σ[ x ∈ X ] Σ[ m ∈ Fin n ] to p (fsuc m) ≡ x) , (n , record { to = λ x → (to p (fsuc x)) , (x , cong (λ y → to p (fsuc y)) refl) ; from = λ ( x , m , p ) → m ; from∘to = λ x → refl ; to∘from = λ ( x , m , p ) → {! p  !}})
      rt   = {!   !}




c : Σ[ X ∈ Set ] Σ[ n ∈ ℕ ] (Fin n ≃ X)
c = Fin 4 , (4 , record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl ; to∘from = λ y → refl })

d : Σ[ x ∈ ℕ ] Fin x
d = {!   !} , {!   !}      
   