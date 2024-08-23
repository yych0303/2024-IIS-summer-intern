module Ring.Data.RingN where

open import Ring.Base

-- Ring ℕ ---------------------------------------------------------------------
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Properties

-- public
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_) public
open import Data.Empty using (⊥; ⊥-elim)

ringℕ : Ring
ringℕ = record
  { R               = ℕ        
  ; R0              = 0        
  ; R1              = 1          
  ; _R+_            = _+_        
  ; _R*_            = _*_            
  ; Rhead           = rh   
  ; Rtail           = rt       
  ; _~_             = _≡_     
  ; ~-R0            = λ { 0 → true ; _ → false }    
  ; ~-refl          = refl          
  ; ~-trans         = trans         
  ; ~-sym           = sym 
  ; Rhead-tail      = ht
  ; Rhead-0h        = 0h 
  ; Rhead-h0        = h0
  ; Rhead-n0        = hn0 
  ; Rtail-01t       = 01t 
  ; Rtail-t01       = t01
  ; Rhead-~         = λ p → cong rh p  
  ; Rtail-~         = λ p → cong rt p  
  ; R+-identityˡ    = λ x → refl
  ; R*-identityˡ    = *-identityˡ
  ; R+-comm         = +-comm
  ; R*-comm         = *-comm
  ; R+-assoc        = +-assoc
  ; R*-assoc        = *-assoc
  ; R*-zeroˡ        = λ x → refl
  ; R*-distribˡ-+   = *-distribˡ-+ 
  ; R+-axeqˡ        = +ae
  ; R*-axeqˡ        = *ae
  }
    where
      rh : ℕ → ℕ
      rh 0       = 0
      rh (suc x) = 1  
      rt : ℕ → ℕ
      rt 0       = 0
      rt (suc x) = x  

      ht : (x : ℕ) → rh x + rt x ≡ x
      ht zero = refl
      ht (suc x) = refl

      0h : (x : ℕ) → (x ≡ 0) → (rh x ≡ 0)
      0h 0 = λ p → cong rh p
      0h (suc x) = λ p → cong rh p
      h0 : (x : ℕ) → (rh x ≡ 0) → (x ≡ 0)
      h0 0 = λ p → refl
      h0 (suc x) = λ p → ⊥-elim (contradiction p)
        where
          contradiction : 1 ≡ 0 → ⊥
          contradiction ()
      hn0 : (x : ℕ) → ¬ (x ≡ 0) → rh x ≡ 1
      hn0 zero = λ x → ⊥-elim (x refl)
      hn0 (suc x) = λ _ → refl
      
      contradiction : (x : ℕ) → suc (suc x) ≡ 1 → ⊥
      contradiction zero = λ () 
      contradiction (suc x) = λ ()    
      proof : (x : ℕ) → suc x ≡ 1 → x ≡ 0
      proof 0 p = refl
      proof (suc x) p = ⊥-elim (contradiction x p)
      tof : (x : ℕ) → (suc x ≡ 0 ⊎ suc x ≡ 1 → x ≡ 0)
      tof x (_⊎_.inj₂ y) = proof x y


      01t : (x : ℕ) → ((x ≡ 0) ⊎ (x ≡ 1)) → (rt x ≡ 0)

      01t zero    = λ p → refl
      01t (suc x) = tof x 

      t01 : (x : ℕ) → (rt x ≡ 0) → ((x ≡ 0) ⊎ (x ≡ 1))
      
      t01 zero = λ p → _⊎_.inj₁ refl
      t01 (suc x) = λ p → _⊎_.inj₂ (cong suc p)
      
      +ae : ∀ (x y z : ℕ) → x ≡ y → (z + x) ≡ (z + y)
      +ae _ _ z p = cong (z +_) p
      *ae : ∀ (x y z : ℕ) → x ≡ y → z * x ≡ z * y
      *ae _ _ z p = cong (z *_) p
 