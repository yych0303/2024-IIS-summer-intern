{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.Func where

open import Ring.Data.RingN
open import Ring.Data.RingLN
open import Ring.Data.RingSt
open import Ring.Data.RingType
open import Data.Fin.Base

-- func ------------------------------------------------------------------

funcℕStℕ : ℕ → St ℕ
funcℕStℕ zero = []
funcℕStℕ (suc n) = [ n ] ∷  funcℕStℕ n 

funcℕListℕ : ℕ → List ℕ


funcℕListℕ = [_]ᶜ
    where
      [_]ᶜ : ℕ → List ℕ
      [ 0 ]ᶜ = []
      [ suc n ]ᶜ = n ∷ [ n ]ᶜ 
--      [ n ]ᶜ = iterate suc 0 n



open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ; join; splitAt) renaming (suc to fsuc ; zero to fzero)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_] )
open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Agda.Primitive
open import Function using (_∘_)

funcℕType : ℕ → (Σ[ X ∈ Set ] Σ[ n ∈ ℕ ] (Fin n ≃ X)) 
funcℕType n = Fin n , n , record  { to = λ z → z
                                  ; from = λ z → z
                                  ; from∘to = λ x → refl
                                  ; to∘from = λ y → refl
                                  }
 