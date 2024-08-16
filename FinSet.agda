{-# OPTIONS --allow-unsolved-metas #-}
module FinSet where
    
open import Agda.Primitive
open import Level


-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive; ≤-refl; +-mono-≤; +-assoc; +-comm)

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
  remove a .([ a ]) here = []
  remove a .(x ++ y) (left {x} {y} a∈x) = (remove a x a∈x) ++ y
  remove a .(y ++ x) (right {y} {x} a∈x) = y ++ (remove a x a∈x)

  open import Data.Nat.Base

  nonept : ∀ {a : A} → (x : List A) → a ∈ x → ¬ (x ≡ []) 
  nonept [] ()
  nonept (x ∷ xs) _ = λ ()

  length-∷ : ∀ (x : A) → (xs : List A) → length (x ∷ xs) ≡ 1 + (length xs)
  length-∷ _ _ = refl

  ≤length-remove : ∀ (a : A) → (x : List A) → (a∈x : a ∈ x) → 1 + length (remove a x a∈x) ≤ length x
  ≤length-remove a .([ a ]) here = s≤s z≤n
  ≤length-remove a .(x ++ y) (left {x} {y} a∈x) = 
      ≤-begin
        1 + length (remove a (x ++ y) (left a∈x))
      ≤⟨ ≤-refl ⟩
        1 + length ((remove a x a∈x) ++ y)
      ≤⟨ ≤-reflexive (cong (1 +_) (length-++ (remove a x a∈x) {y})) ⟩
        1 + length (remove a x a∈x) + length y
      ≤⟨ +-mono-≤ (≤length-remove a x a∈x) (≤-refl {length y}) ⟩
        length x + length y
      ≤⟨ ≤-reflexive (sym (length-++ x {y})) ⟩
        length (x ++ y)
      ≤-∎
  ≤length-remove a .(y ++ x) (right {y} {x} a∈x) = 
      ≤-begin
        1 + length (remove a (y ++ x) (right a∈x))
      ≤⟨ ≤-refl ⟩
        1 + length (y ++ (remove a x a∈x))
      ≤⟨ ≤-reflexive (cong (1 +_) (length-++ y {remove a x a∈x})) ⟩
        1 + length y + length (remove a x a∈x)
      ≤⟨ ≤-reflexive ( cong (_+ length (remove a x a∈x)) (+-comm 1 (length y))) ⟩
        length y + 1 + length (remove a x a∈x)
      ≤⟨ ≤-reflexive ( +-assoc (length y) 1 (length (remove a x a∈x)) ) ⟩
        length y + (1 + length (remove a x a∈x))
      ≤⟨ +-mono-≤ (≤-refl {length y}) (≤length-remove a x a∈x) ⟩
        length y + length x
      ≤⟨ ≤-reflexive (sym (length-++ y {x})) ⟩
        length (y ++ x)
      ≤-∎


  
  
  
  swicth-left : (x : List A)
              → (a : A) → (a∈x : a ∈ x)
              → ((b : A) → (b∈x' : b ∈ (remove a x a∈x)) → b ∈ x)
  swicth-left = {!   !}
  ∈-remove  : (x : List A)
              → (a : A) → (a∈x : a ∈ x)
              → ((b : A) → (b∈x' : b ∈ (remove a x a∈x)) → b ∈ x)
  ∈-remove .([ a ]) a here b b∈x' = left b∈x'
  ∈-remove .(x ++ y) a (left {x} {y} a∈x) b b∈x' = left {! ∈-remove    !}
  ∈-remove .(y ++ x) a (right {y} {x} a∈x) b b∈x' = {!   !}


 -- once-remove : (x : List A)
 --             → (once : (a : A) → a ∈ x → a ∈₁ x)
 --             → (a : A) → (a∈x : a ∈ x)
 --             → ((b : A) → (b∈x' : b ∈ (remove a x a∈x)) → b ∈₁ (remove a x a∈x))
 -- once-remove .([ a ]) once a here b ()
 -- once-remove .(x ++ y) once a (left {x} {y} a∈x) b b∈x'y with once b ? 
 -- ...                                                         | here₁    = {!   !}
 -- ...                                                         | left₁ _  = {!   !}
 -- ...                                                         | right₁ _ = ?




  -- once-remove .(y ++ x) once a (right {y} {x} a∈x) = {!   !}




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

  once-∷  : (a : A) → (x : List A)
          → (once : (o : A) → o ∈ ([ a ] ++ x) → o ∈₁ ([ a ] ++ x))
          → ((b : A) → b ∈ x → b ∈₁ x)
  
  once-∷ a x once b b∈x with once b (right {b} {[ a ]} {x} b∈x)
  ...                       | here₁    = ? 
  ...                      | left₁ {b} {[ a ]} {x} _  = ?
  ...                      | right₁ {} {} _ = ?  
  --once-∷ a .([ b ]) once b here = here₁
  --once-∷ a .(x ++ y) once b (left {x} {y} b∈x) with once b (right {_} {(x ++ y)} (left {x} {y} b∈x))
  --...                                             | here₁    = ? 
  --...                                             | left₁ _  = ?
  --...                                             | right₁ _ = ?  
  --once-∷ a .(y ++ x) once b (right {y} {x} b∈x) = {!   !}

  contain-∷ : (a : A) → (list : List A)
            → (once : (a : A) → a ∈ (a ∷ list) → a ∈₁ (a ∷ list))
            → (l : List A)
            → (contain : (b : A) → (b ∈ (a ∷ list)) → b ∈ l)
            → ((c : A) → (c ∈ list) → c ∈ (remove a l (contain a (left here))))
  contain-∷ = {!   !}
      
 --  proof-ss-minimal  : (list : List A)
 --                    → (once : (y : A) → y ∈ list → y ∈₁ list)
 --                    → (l : List A)
 --                    → (subset : (x : A) → (x ∈ l) → x ∈ list) → length list ≤ length l
 --  proof-ss-minimal = {!   !}

  proof-minimal : (list : List A)
                → (once : (a : A) → a ∈ list → a ∈₁ list)
                → (l : List A)
                → (contain : (b : A) → (b ∈ list) → b ∈ l)
                → length list ≤ length l
  proof-minimal [] O l C = z≤n
  proof-minimal (a ∷ list) O l C = 
      ≤-begin
        length (a ∷ list)
      ≤⟨ ≤-reflexive (length-∷ a list) ⟩
        1 + (length list)
      ≤⟨ s≤s (proof-minimal list {!   !} (remove a l (C a (left here))) {! contain-∷ a list O l C  !}) ⟩
        1 + length (remove a l (C a (left here)))
      ≤⟨ ≤length-remove a l ( C a (left here) ) ⟩
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

 