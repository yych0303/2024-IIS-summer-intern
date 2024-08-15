{-# OPTIONS --allow-unsolved-metas #-}
module FinSet where
    
open import Agda.Primitive
open import Level


-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym)


open import Data.List.Base public
open import Data.List.Properties




infix 0 _≃_
record _≃_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_ public



module _ {i : Level} {A : Set i} where
    
    
  


  infix 7 _∈_
  infix 7 _∉_

  data _∈_ (a : A) : (x : List A) → Set i where
    here  : a ∈ [ a ]
    left  : ∀ {x y} → (a∈x : a ∈ x) → a ∈ (x ++ y)
    right : ∀ {x y} → (a∈y : a ∈ y) → a ∈ (x ++ y)
  
  open import Relation.Nullary using (Dec; ¬_) public

  _∉_ : (a : A) → (x : List A) → Set i
  a ∉ x = ¬ (a ∈ x)
  
  data _∈₁_ (a : A) : (x : List A) → Set i where
    here₁  : a ∈₁ [ a ]
    left₁  : ∀ {x y} → (a∈₁x : a ∈₁ x) → (a∉y : a ∉ y) → a ∈₁ (x ++ y) 
    right₁ : ∀ {x y} → (a∉x : a ∉ x) → (a∈₁y : a ∈₁ y) → a ∈₁ (x ++ y)

  remove : (a : A) → (x : List A) → (a∈x : a ∈ x) → List A
  remove a [] ()
  remove a (x ∷ xs) a∈x = {!   !}

  open import Data.Nat.Base

  nonept : ∀ {a : A} → (x : List A) → a ∈ x → ¬ (x ≡ []) 
  nonept [] ()
  nonept (x ∷ xs) _ = λ ()

  length-∷ : ∀ (x : A) → (xs : List A) → length (x ∷ xs) ≡ 1 + (length xs)
  length-∷ _ _ = refl

  ≤length-remove : ∀ (a : A) → (x : List A) → (a∈x : a ∈ x) → 1 + length (remove a x a∈x) ≤ length x
  ≤length-remove = {!   !}

  proof-once-prop : (list : List A)
               (a : A)
               (once : (y : A) → y ∈ list → y ∈₁ list)
               → ((x : A) → (x ∈ remove a list _) → x ∈₁ remove a list _)
  proof-once-prop = {!   !}

-----

  proof-exist-ss : (list : List A)
               (exist : (x : A) → x ∈ list)
               (once : (y : A) → y ∈ list → y ∈₁ list)
               (l : List A)
               (l-exist : (z : A) → z ∈ l) → ((x : A) → (x ∈ l) → x ∈₁ list)
  proof-exist-ss = {!   !}

  proof-remove-ss : (list l : List A) 
               (a : A)
               (once : (y : A) → y ∈ list → y ∈₁ list)
               (subset : (x : A) → (x ∈ l) → x ∈ list) → ((x : A) → (x ∈ remove a l _) → x ∈₁ remove a list _)
  proof-remove-ss = {!   !} -- not delete a

  
  proof-ss-minimal : (list : List A)
               (once : (y : A) → y ∈ list → y ∈₁ list)
               (l : List A)
               (subset : (x : A) → (x ∈ l) → x ∈ list) → length list ≤ length l
  proof-ss-minimal = {!   !}

  proof-minimal : (list : List A)
               (exist : (x : A) → x ∈ list)
               (once : (y : A) → y ∈ list → y ∈₁ list)
               (l : List A)
               (p : (z : A) → z ∈ l) → length list ≤ length l
  
  proof-minimal [] e o l p = z≤n
  proof-minimal (x ∷ list) e o l p = 
      ≤-begin
        length (x ∷ list)
      ≤⟨ ≤-reflexive (length-∷ x list) ⟩
        1 + (length list)
      ≤⟨ {!   !} ⟩
        {!   !}
      ≤⟨ {!   !} ⟩
        1 + length (remove x l (p x))
      ≤⟨ ≤length-remove x l (p x) ⟩
        length l
      ≤-∎
      
    
    
    -- {!  proof-minimal list !}





open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (Dec; ¬_) public
open import Data.Sum using (_⊎_) public
open import Data.Empty


congm : ∀ {i : Level} {A B : Set i} {b : B} {s : List B} → (f : B → A) → (b∈s : b ∈ s) → (f b) ∈ (map f s)
congm {b = b} {s = .([ b ])} f here = here
congm {b = b} {s = .(x ++ y)} f (left {x = x} {y = y} b∈x) =  subst (_∈_ (f b)) (sym (map-++ f x y)) (left {x = map f x} {y = map f y} (congm f b∈x))
congm {b = b} {s = .(x ++ y)} f (right {x = x} {y = y} b∈y) = subst (_∈_ (f b)) (sym (map-++ f x y)) (right {x = map f x} {y = map f y} (congm f b∈y))

substm : ∀ {i : Level} {A : Set i} {a aa : A} {x : List A} → a ≡ aa → (a∈x : a ∈ x) → aa ∈ x
substm refl a∈x = a∈x




open import Data.Nat.Base


record FinSet {i : Level} : Set (lsuc i) where
  field
    Carrier : Set i
    list : List Carrier
    proof : (x : Carrier) → x ∈ list
    minimal : (l : List Carrier) → ((x : Carrier) → x ∈ l) → length list ≤ length l
    -- once : (x : Carrier) → x ∈ list → x ∈₁ list
open FinSet public

