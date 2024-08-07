{-# OPTIONS --allow-unsolved-metas #-}
module Rings where
-- Rings
{-

record
{ R               = ?              
; R0              = r0             
; R1              = r1             
; Rpre            = rpre           
; _R+_            = _r+_           
; _R*_            = _r*_           
; RIdx            = λ _ → ?          
; _≃_             = ?           
; isDecEquivR0    = ?    
; refl            = ?          
; trans           = ?         
; sym             = ?           
; zero-pre-one    = ?
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)


ringℕ : Ring
ringℕ = record
  { R               = ℕ        
  ; R0              = 0        
  ; R1              = 1        
  ; Rpre            = rpre        
  ; _R+_            = _+_        
  ; _R*_            = _*_            
  ; _≃_             = _≡_     
  ; isDecEquivR0    = λ x → 0 ≟ x    
  ; refl            = refl          
  ; trans           = trans         
  ; sym             = sym           
  ; zero-pre-one    = refl
  ; zero-identity+  = refl
  ; one-identity*   = {!   !}
  ; comm+           = {!   !}
  ; comm*           = {!   !}
  ; assoc+          = {!   !}
  ; assoc*          = {!   !}
  ; distrib         = {!   !} 
  }
    where
      rpre : ℕ → ℕ
      rpre 0       = 0
      rpre (suc x) = x  

evalℕ : Term ℕ → ℕ
evalℕ = eval ringℕ


-- Ring (List ℕ) -----------------------------------------------


ringListℕ : Ring
ringListℕ = record  
  { R               = List ℕ          
  ; R0              = []        
  ; R1              = [ 0 ]          
  ; Rpre            = rpre
  ; _R+_            = r+          
  ; _R*_            = r*                
  ; _≃_             = {!   !}    
  ; isDecEquivR0    = {!   !}
  ; refl            = {!   !}          
  ; trans           = {!   !}         
  ; sym             = {!   !}           
  ; zero-pre-one    = {!   !}
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
      rpre  : List ℕ → List ℕ 
      rpre []      = []
      rpre (x ∷ l) = l
      r+    = λ xs ys → xs ++ (map ((length xs) +_) ys)
      r*    = λ xs ys → foldl (λ acc x → (r+ ys acc)) r0 xs


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
  ; Rpre            = rpre
  ; _R+_            = r+
  ; _R*_            = r*
  ; _≃_             = {!   !}    
  ; isDecEquivR0     = {!   !}
  ; refl            = {!   !}          
  ; trans           = {!   !}         
  ; sym             = {!   !}           
  ; zero-pre-one    = {!   !}
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
      rpre : (List (List A)) → List (List A)
      rpre [] = []
      rpre (x ∷ xs) = xs

      r+ : {A : Set} → St A → St A → St A
      r+ = _++_
      r* : {A : Set} → St A → St A → St A
      r* = λ xs ys → concatMap (λ x → map (x ++_) ys ) xs

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




 
  