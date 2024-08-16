{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.RingFinSet where

open import Ring.Base 
-- Ring FinSet ---------------------------------------------------- 

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym) public


open import Data.List.Base public
open import Data.List.Properties



open import Data.Fin using (Fin) renaming (suc to fsuc ; zero to fzero)
open import Data.Fin.Properties

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂) public

-- Files -----------------------------------------------------------------
open import FinSet public



-- ring ------------------------------------------------------

ringFinSet : Ring
ringFinSet = record 
  { R               = FinSet --       
  ; R0              = record { Carrier = Fin 0 ; list = [] ; exist = λ () ; minimal = λ l _ → z≤n }             
  ; R1              = record { Carrier = Fin 1 ; list = [ fzero ] ; exist = λ { fzero → here } ; minimal = λ l p → {!  !} }--     
  ; Rhead           = {!   !} --
  ; Rtail           = {!   !} --       
  ; _R+_            = λ X Y → record { Carrier = Carrier X ⊎ Carrier Y ; list = (map inj₁ (list X)) ++ (map inj₂ (list Y)) ; exist = λ { (inj₁ z) → left (congm inj₁ (exist X z)) ; (inj₂ z) → right (congm inj₂ (exist Y z))} ; minimal = λ l p → {!   !}  }         
  ; _R*_            = λ X Y → record { Carrier = Carrier X × Carrier Y ; list = cartesianProduct (list X) (list Y) ; exist = {!   !} ; minimal = {!   !} }             
  ; _~_             = λ X Y → Carrier X ≃ Carrier Y           
  ; ~-R0            = λ X → null (list X)
  ; ~-refl          = record { to = λ z → z ; from = λ z → z ; from∘to = λ z → refl ; to∘from = λ z → refl }         
  ; ~-trans         = λ P Q → record { to = λ a → to Q (to P a) ; from = λ c →  from P (from Q c) ; from∘to = λ a → trans (cong (from P) (from∘to Q _)) (trans (from∘to P _) refl) ; to∘from = λ c → trans (cong (to Q) (to∘from P _)) (trans (to∘from Q _) refl) }        
  ; ~-sym           = λ P → record { to = from P ; from = to P ; from∘to = to∘from P ; to∘from = from∘to P }
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
      



    