module Rings where
-- Rings
{-

ringℕ
ringSt
ringListℕ

-}


open import N-cal

-- Ring ℕ ---------------------------------------------------------------------
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)


ringℕ : Ring
ringℕ = record
  { R    = ℕ
  ; R0   = 0
  ; R1   = 1
  ; _R+_ = _+_
  ; _R*_ = _*_
  ; RIdx = λ x → 0
  ; RP   = permutation
  ; RC   = combination
  ; _≈_  = _≡_
  ; isEq = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
    where      
      permutation : ℕ → ℕ → ℕ
      permutation _ 0 = 1
      permutation 0 _ = 0
      permutation (suc i) (suc j) = (suc i) * permutation i j 

      combination : ℕ → ℕ → ℕ
      combination _ 0 = 1
      combination 0 _ = 0
      combination (suc i) (suc j) = combination i j + combination i (suc j) 



evalℕ : Term ℕ → ℕ
evalℕ = eval ringℕ


-- Ring (List ℕ) -----------------------------------------------


ringListℕ : Ring
ringListℕ = record  
  { R    = List ℕ
  ; R0   = r0
  ; R1   = r1
  ; _R+_ = r+
  ; _R*_ = r*
  ; RIdx = λ x → []
  ; RP   = rP
  ; RC   = rC
  ; _≈_  = R≈
  ; isEq = record
    { refl  = {!   !}
    ; sym   = {!   !}
    ; trans = {!   !}
    }
  }
    where
      r0 = []
      r1 = [ 0 ]
      r+ = λ xs ys → xs ++ (map ((length xs) +_) ys)
      r*  = λ xs ys → foldl (λ acc x → (r+ ys acc)) r0 xs
      rP : List ℕ → List ℕ → List ℕ
      rP _ [] = r1
      rP [] _ = r0
      rP (x ∷ xs) (y ∷ ys) = r* (x ∷ xs) (rP xs ys)
      
      rC : List ℕ → List ℕ → List ℕ
      rC _ [] = r1
      rC [] _ = r0
      rC (x ∷ xs) (y ∷ ys) = r+ (rC xs ys) (rC xs (y ∷ ys))

      R≈ = {!   !}




      

evalListℕ : Term (List ℕ) → List ℕ
evalListℕ = eval ringListℕ



-- Ring (St A) ---------------------------------------------------- 



ringSt : Set → Ring
ringSt A = record
  { R    = St A
  ; R0   = r0
  ; R1   = r1
  ; _R+_ = r+
  ; _R*_ = r*
  ; RIdx = λ x → []
  ; RP   = rP
  ; RC   = rC  
  ; _≈_  = {!   !}
  ; isEq = record
    { refl  = {!   !}
    ; sym   = {!   !}
    ; trans = {!   !}
    }

  }
    where
      r0 : {A : Set} → St A
      r0 = []
      r1 : {A : Set} → St A
      r1 = [ [] ]
      r+ : {A : Set} → St A → St A → St A
      r+ = _++_
      r* : {A : Set} → St A → St A → St A
      r* = λ xs ys → concatMap (λ x → map (x ++_) ys ) xs
      
      rP : {A : Set} → St A → St A → St A
      rP _ []  = r1
      rP [] _  = r0
      rP (x ∷ xs) (y ∷ ys) = r* (x ∷ xs)  (rP xs ys)

      rC : {A : Set} → St A → St A → St A
      rC _ [] = r1
      rC [] _ = r0
      rC (x ∷ xs) (y ∷ ys) = r+ (r* [ x ] (rC xs ys)) (rC xs (y ∷ ys))
  

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





