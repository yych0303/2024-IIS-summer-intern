{-# OPTIONS --allow-unsolved-metas #-}
module Ring.Data.RingKu where

open import Ring.Base 
-- Ring Type ---------------------------------------------------- 

open import Agda.Primitive
open import Level using (_⊔_)
open import Level
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Function using (_∘_)


-- open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_] ) public
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym) public


infix 0 _≃_
record _≃_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_





open import Data.List.Base public
open import Data.List.Properties
infix 7 _∈_


data _∈_ {i : Level} {A : Set i} (a : A) : (x : List A) → Set i where
  here  : a ∈ [ a ]
  left  : ∀ {x y} → (a∈x : a ∈ x) → a ∈ (x ++ y)
  right : ∀ {x y} → (a∈y : a ∈ y) → a ∈ (x ++ y)
  

  
congm : ∀ {i : Level} {A B : Set i} {b : B} {s : List B} → (f : B → A) → (b∈s : b ∈ s) → (f b) ∈ (map f s)
congm {b = b} {s = .([ b ])} f here = here
congm {b = b} {s = .(x ++ y)} f (left {x = x} {y = y} b∈x) =  subst (_∈_ (f b)) (sym (map-++ f x y)) (left {x = map f x} {y = map f y} (congm f b∈x))
congm {b = b} {s = .(x ++ y)} f (right {x = x} {y = y} b∈y) = subst (_∈_ (f b)) (sym (map-++ f x y)) (right {x = map f x} {y = map f y} (congm f b∈y))

record FinSet {i : Level} : Set (lsuc i) where
  field
    Carrier : Set i
    list : List Carrier
    proof : (x : Carrier) → x ∈ list
open FinSet



open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂) public
-- Membership relation

open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ; join; splitAt) renaming (suc to fsuc ; zero to fzero)
open import Data.Fin.Properties
ringType : Ring
ringType = record 
  { R               = FinSet --       
  ; R0              = record { Carrier = Fin 0 ; list = [] ; proof = λ () }             
  ; R1              = record { Carrier = Fin 1 ; list = [ fzero ] ; proof = λ { fzero → here } } --     
  ; Rhead           = {!   !} --
  ; Rtail           = {!   !} --       
  ; _R+_            = λ x y → record { Carrier = Carrier x ⊎ Carrier y ; list = (map inj₁ (list x)) ++ (map inj₂ (list y)) ; proof = λ { (inj₁ z) → left (congm inj₁ (proof x z)) ; (inj₂ z) → right (congm inj₂ (proof y z))} }         
  ; _R*_            = λ x y → record { Carrier = Carrier x × Carrier y ; list = cartesianProduct (list x) (list y) ; proof = {!   !} }             
  ; _~_             = λ x y → Carrier x ≃ Carrier y           
  ; ~-R0            = {!   !} --λ { ( _ , 0 , _ ) → true ; _ → false }    
  ; ~-refl          = {!   !} --record { to = λ z → z ; from = λ z → z ; from∘to = λ x₁ → refl ; to∘from = λ y → refl }         
  ; ~-trans         = {!   !} --λ p q → record { to = (to q) ∘ (to p) ; from = (from p) ∘ (from q) ; from∘to = {!   !} ; to∘from = {!   !} }         
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
      



