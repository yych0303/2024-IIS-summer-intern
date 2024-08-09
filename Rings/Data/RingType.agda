{-# OPTIONS --allow-unsolved-metas #-}
module Rings.Data.RingType where

open import Rings.CommutativeRing
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
  

-}

