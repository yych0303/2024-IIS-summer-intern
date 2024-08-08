{-# OPTIONS --allow-unsolved-metas #-}
module Rings where
-- Rings
{-

record
{ R               = ?              
; R0              = r0             
; R1              = r1     
; Rhead           = ?     
; Rtail           = ?        
; _R+_            = _r+_           
; _R*_            = _r*_           
; RIdx            = λ _ → ?          
; _≃_             = ?           
; isDecEquivR0    = ?    
; refl            = ?          
; trans           = ?         
; sym             = ?
; head-tail       = ?
; head-0          = ?
; head-n0         = ? 
; tail-01         = ? 
; zero-identity+  = ?
; one-identity*   = ?
; comm+           = ?
; comm*           = ?
; assoc+          = ?
; assoc*          = ?
; distrib         = ? 
}
  where
    r0   = ?
    r1   = ?
    rpre = ?
    _r+_ = ?
    _r*_ = ?    


-}


open import N-cal


-- Ring ℕ ---------------------------------------------------------------------
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Properties

ringℕ : Ring
ringℕ = record
  { R               = ℕ        
  ; R0              = 0        
  ; R1              = 1          
  ; Rhead           = rh   
  ; Rtail           = rt       
  ; _R+_            = _+_        
  ; _R*_            = _*_            
  ; _≃_             = _≡_     
  ; isDecEquivR0    = λ x → 0 ≟ x    
  ; refl            = refl          
  ; trans           = trans         
  ; sym             = sym 
  ; head-tail       = ht
  ; head-0          = h0
  ; head-n0         = hn0 
  ; tail-01         = t01
  ; zero-identity+  = λ x → refl
  ; one-identity*   = *-identityˡ
  ; comm+           = +-comm
  ; comm*           = *-comm
  ; assoc+          = +-assoc
  ; assoc*          = *-assoc
  ; distrib         = *-distribˡ-+ 
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

      h0 : (x : ℕ) → (x ≡ 0) ↔ (rh x ≡ 0)
      h0 0 = record
        { to   = λ p → cong rh p
        ; from = λ p → refl
        }
      h0 (suc x) = record
        { to   = λ p → cong rh p
        ; from = λ p → ⊥-elim (contradiction p)
        }
        where
          contradiction : 1 ≡ 0 → ⊥
          contradiction ()
      hn0 : (x : ℕ) → ¬ (x ≡ 0) → rh x ≡ 1
      hn0 zero = λ x → ⊥-elim (x refl)
      hn0 (suc x) = λ _ → refl
      t01 : (x : ℕ) → ((x ≡ 0) ⊎ (x ≡ 1)) ↔ (rt x ≡ 0)
      t01 zero    = record
        { to   = λ p → refl
        ; from = λ p → _⊎_.inj₁ refl
        }
      t01 (suc x) = record
        { to   = tof x 
        ; from = λ p → _⊎_.inj₂ (cong suc p)
        }
        where
          contradiction : (x : ℕ) → suc (suc x) ≡ 1 → ⊥
          contradiction zero = λ () 
          contradiction (suc x) = λ ()    
          proof : (x : ℕ) → suc x ≡ 1 → x ≡ 0
          proof 0 p = refl
          proof (suc x) p = ⊥-elim (contradiction x p)
          tof : (x : ℕ) → (suc x ≡ 0 ⊎ suc x ≡ 1 → x ≡ 0)
          tof x (_⊎_.inj₂ y) = proof x y

      
evalℕ : Term ℕ → ℕ
evalℕ = eval ringℕ


-- Ring (List ℕ) -----------------------------------------------
open import Relation.Nullary using (yes; no)

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


evalListℕ : Term (List ℕ) → List ℕ
evalListℕ = eval ringListℕ



-- Ring (St A) ---------------------------------------------------- 

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

evalSt : {A : Set} → Term (St A) → St A
evalSt {A} = eval (ringSt A)



-- Ring Type ---------------------------------------------------- 
{-

Type = Set

open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ) renaming (suc to fsuc ; zero to fzero)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)


ringType : Ring
ringType = record
  { R    = Type
  ; R0   = r0
  ; R1   = r1
  ; _R+_ = r+
  ; _R*_ = r*
  ; RIdx = λ x → r0
  ; RP   = {!   !}
  ; RC   = {!   !} 
  }
    where
      r0 = Fin 0
      r1 = Fin 1
      r+ = _⊎_
      r* = _×_
      
      rP : Type → Type → Type
      rP _ r0  = r1
      rP r0 _  = r0
      -- rP (Fin n) (Fin k)  = r* ? ?

      rC : Type → Type → Type
      rC _ r0 = r1
      rC r0 _ = r0
      -- rC (x ∷ xs) (y ∷ ys) = r+ (r* [ x ] (rC xs ys)) (rC xs (y ∷ ys))
  

evalType : Term Type → Type
evalType = eval ringType

-}


-- func ------------------------------------------------------------------

funcℕStℕ : ℕ → St ℕ
funcℕStℕ = λ n → map [_] (iterate suc 0 n)

funcℕListℕ : ℕ → List ℕ
funcℕListℕ = [_]ᶜ
    where
      [_]ᶜ : ℕ → List ℕ
      [ n ]ᶜ = iterate suc 0 n




       
       