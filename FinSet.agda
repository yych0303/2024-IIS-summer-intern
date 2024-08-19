{-# OPTIONS --allow-unsolved-metas #-}
module FinSet where
    
open import Agda.Primitive
open import Level
open import Data.Empty using (⊥-elim)

-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive; ≤-refl; +-mono-≤; +-assoc; +-comm)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym)


open import Data.List.Base public
open import Data.List.Properties


module _ {i : Level} {A : Set i} where
  open import Relation.Nullary using (Dec; ¬_) public

  infix 7 _∈_
  infix 7 _∉_

  data _∈_ (a : A) : (x : List A) → Set i where
    here  : a ∈ [ a ]
    left  : ∀ {x y} → (a∈x : a ∈ x) → a ∈ (x ++ y)
    right : ∀ {x y} → (a∈y : a ∈ y) → a ∈ (x ++ y)
  

  _∉_ : (a : A) → (x : List A) → Set i
  a ∉ x = ¬ (a ∈ x)
  
  ∉-ept : ∀ {a : A} → a ∉ []
  ∉-ept {a} ()
  
  -- appending-∈'

  data _∈'_ (a : A) : (x : List A) → Set i where
    here'  : ∀ {x} → a ∈' (a ∷ x)
    there' : ∀ {b} {x} → (a∈x : a ∈' x) → a ∈' (b ∷ x)
  
  ∈'⇒∈ : ∀ {a : A} {x : List A} → a ∈' x → a ∈ x
  ∈'⇒∈ {a} {.(a ∷ _)} here' = left here
  ∈'⇒∈ {a} {.(_ ∷ _)} (there' p) = right (∈'⇒∈ p)
  
  {-# NON_TERMINATING #-}
  ∈⇒∈' : ∀ {a : A} {x : List A} → a ∈ x → a ∈' x
  ∈⇒∈' {a} {.([ a ])} here = here'
  ∈⇒∈' {a} {.([] ++ x)} (right {[]} {x} a∈x) = ∈⇒∈' a∈x
  ∈⇒∈' {a} {.((b ∷ y) ++ x)} (right {b ∷ y} {x} a∈x) = there' {a} {b} (∈⇒∈' {a} {y ++ x} (right {a} {y} {x} a∈x))
  ∈⇒∈' {a} {.([] ++ y)} (left {[]} {y} a∈x) = ⊥-elim (∉-ept a∈x)
  ∈⇒∈' {a} {.((x ∷ x₁) ++ y)} (left {x ∷ x₁} {y} a∈x) with ∈⇒∈' a∈x
  ... | here' = here'   
  ... | there' a∈'x' = there' (∈⇒∈' (left (∈'⇒∈ a∈'x')))
    


  data _∈₁_ (a : A) : (x : List A) → Set i where
    here₁  : a ∈₁ [ a ]
    left₁  : ∀ {x y} → (a∈₁x : a ∈₁ x) → (a∉y : a ∉ y) → a ∈₁ (x ++ y) 
    right₁ : ∀ {x y} → (a∉x : a ∉ x) → (a∈₁y : a ∈₁ y) → a ∈₁ (x ++ y)

  -- appending-∈₁'

  data _∈₁'_ (a : A) : (x : List A) → Set i where
    here₁'  : ∀ {y} → (a∉y : a ∉ y) → a ∈₁' (a ∷ y) 
    there₁' : ∀ {b y} → (a∉x : a ∉ [ b ]) → (a∈₁'y : a ∈₁' y) → a ∈₁' (b ∷ y)


  ∈₁⇒∈ : ∀ {a : A} {x : List A} → a ∈₁ x → a ∈ x
  ∈₁⇒∈ here₁ = here
  ∈₁⇒∈ (left₁ a∈₁x a∉y) = left (∈₁⇒∈ a∈₁x)
  ∈₁⇒∈ (right₁ a∉x a∈₁x) = right (∈₁⇒∈ a∈₁x)

  ∉⇒∉h : ∀ {a b : A} {x : List A} → a ∉ (b ∷ x) → a ∉ [ b ]
  ∉⇒∉h a∉bx a∈b = a∉bx (left a∈b)  

  ∉⇒∉t : ∀ {a b : A} {x : List A}
      → (a∉bx : a ∉ (b ∷ x))
      → (a ∉ x)
  ∉⇒∉t {b = b} a∉bx a∈x = a∉bx (right {x = b ∷ []} a∈x) 

  ∉∉⇒∉ : ∀ {a : A} {x y : List A}
      → (a∉x : a ∉ x)
      → (a∉y : a ∉ y)
      → (a ∉ (x ++ y))
  ∉∉⇒∉ {x = []} a∉x a∉y a∈xy = a∉y a∈xy
  ∉∉⇒∉ {x = x ∷ x'} a∉x a∉y a∈xy with ∈⇒∈' a∈xy
  ... | there' a∈xy'  = ∉∉⇒∉ {x = x'} (∉⇒∉t a∉x) a∉y (∈'⇒∈ a∈xy')
  ... | here'         = a∉x (left (here))



  ∈₁'⇒∈₁ : ∀ {a : A} {x : List A} → a ∈₁' x → a ∈₁ x
  ∈₁'⇒∈₁ (here₁' a∉y) = left₁ here₁ a∉y
  ∈₁'⇒∈₁ (there₁' a∉x a∈₁'x) = right₁ a∉x (∈₁'⇒∈₁ a∈₁'x) 

  {-# NON_TERMINATING #-}
  ∈₁⇒∈₁' : ∀ {a : A} {x : List A} → a ∈₁ x → a ∈₁' x
  ∈₁⇒∈₁' (right₁ {x = []} a∉y a∈₁x) = ∈₁⇒∈₁' a∈₁x
  ∈₁⇒∈₁' (right₁ {x = y ∷ y'} a∉yy' a∈₁x) = there₁' (∉⇒∉h a∉yy') (∈₁⇒∈₁' (right₁ (∉⇒∉t a∉yy') a∈₁x))
  ∈₁⇒∈₁' here₁ = here₁' ∉-ept
  ∈₁⇒∈₁' (left₁ {x = []} a∈₁x a∉y) = ⊥-elim (∉-ept (∈₁⇒∈ a∈₁x))
  ∈₁⇒∈₁' (left₁ {x = x ∷ x'} a∈₁x a∉y) with ∈₁⇒∈₁' a∈₁x
  ... | here₁' a∉x' = here₁' (∉∉⇒∉ a∉x' a∉y)   
  ... | there₁' a∉x a∈₁'x' = there₁' a∉x (∈₁⇒∈₁' (left₁ (∈₁'⇒∈₁ a∈₁'x') a∉y))
    
  
  ---

  
  nonept : ∀ {a : A} → (x : List A) → a ∈ x → ¬ (x ≡ []) 
  nonept [] ()
  nonept (x ∷ xs) _ = λ ()

  remove : (a : A) → (x : List A) → (a∈x : a ∈ x) → List A
  remove a .([ a ]) here = []
  remove a .(x ++ y) (left {x} {y} a∈x) = (remove a x a∈x) ++ y
  remove a .(y ++ x) (right {y} {x} a∈x) = y ++ (remove a x a∈x)

  remove' : (a : A) → (x : List A) → (a∈'x : a ∈' x) → List A
  remove' a .(a ∷ x) (here' {x = x}) = x
  remove' a .(b ∷ x) (there' {b = b} {x = x} a∈'x) = b ∷ remove' a x a∈'x

--------------------------------------------

  ∈₁-∷ : ∀ {a b : A} {x : List A}
        → (a∉b : a ∉ [ b ]) 
        → (a∈₁bx : a ∈₁ (b ∷ x))
        → (a ∈₁ x)
  ∈₁-∷ a∉b a∈₁bx with ∈₁⇒∈₁' a∈₁bx
  ... | here₁' _ = ⊥-elim (a∉b here)  
  ... | there₁' _ a∈₁'x = ∈₁'⇒∈₁ a∈₁'x

  notfst : ∀ {a b : A} {x : List A}
        → (a∈₁bx : a ∈₁ (b ∷ x))
        → (a∈x : a ∈ x)
        → (a ∉ [ b ]) 
  notfst a∈₁bx a∈x a∈b with ∈₁⇒∈₁' a∈₁bx
  ... | here₁' a∉x = a∉x a∈x
  ... | there₁' a∉b _ = a∉b a∈b


  once-∷  : (b : A) (x : List A)
          → (once : (a₁ : A) → a₁ ∈ (b ∷ x) → a₁ ∈₁ (b ∷ x))
          → ((a : A) → a ∈ x → a ∈₁ x)
  once-∷ b x once a a∈x = ∈₁-∷ {a = a} {b = b} a∉b a∈₁bx
    where
      a∈₁bx : a ∈₁ (b ∷ x)
      a∈₁bx = once a (right a∈x)
      a∉b : a ∉ [ b ]
      a∉b = notfst a∈₁bx a∈x

  ---------------------------------------------------------------------------------------------
  

  ∈'-remove'  : ∀ {b c : A} {l : List A}
              → (b∈'l : b ∈' l)
              → (c∈'l : c ∈' l)
              → (c∉b : c ∉ [ b ])
              → (c ∈' (remove' b l b∈'l))
  ∈'-remove' here' here' c∉b = ⊥-elim (c∉b here)
  ∈'-remove' here' (there' c∈'l) c∉b = c∈'l
  ∈'-remove' (there' b∈'l) here' c∉b = here'
  ∈'-remove' (there' b∈'l) (there' c∈'l) c∉b = there' (∈'-remove' b∈'l c∈'l c∉b)
  
  contain-∷ : (b : A) → (list : List A)
            → (once : (a₁ : A) → a₁ ∈ (b ∷ list) → a₁ ∈₁ (b ∷ list))
            → (l : List A)
            → (contain : (a : A) → (a ∈' (b ∷ list)) → a ∈' l)
            → ((c : A) → (c ∈' list) → c ∈' (remove' b l (contain b here')))
  contain-∷ b list once [] contain c c∈'list = ⊥-elim (∉-ept (∈'⇒∈ (contain c (there' c∈'list))))
  contain-∷ b list once (b' ∷ l) contain c c∈'list = ∈'-remove' b∈'l c∈'b'l (notfst (once c c∈blist) (∈'⇒∈ c∈'list))
    where
      c∈'blist : c ∈' (b ∷ list)
      c∈'blist = there' c∈'list
      c∈blist : c ∈ (b ∷ list)
      c∈blist = ∈'⇒∈ c∈'blist
      b∈'l = contain b here'
      c∈'b'l : c ∈' (b' ∷ l)
      c∈'b'l = contain c (c∈'blist)

 ----------------------------------

  open import Data.Nat.Base
  
  length-∷ : ∀ (x : A) → (xs : List A) → length (x ∷ xs) ≡ 1 + (length xs)
  length-∷ _ _ = refl

  ≤length-remove' : ∀ (a : A) → (x : List A) → (a∈'x : a ∈' x) → 1 + length (remove' a x a∈'x) ≤ length x
  ≤length-remove' a .(a ∷ x) (here' {x = x}) = 
      ≤-begin
        1 + length (x)
      ≤⟨ ≤-reflexive (sym (length-∷ a x)) ⟩
        length (a ∷ x)
      ≤-∎
  ≤length-remove' a .(b ∷ x) (there' {b = b} {x = x} a∈'x) =
      ≤-begin
        1 + length (b ∷ (remove' a x a∈'x))
      ≤⟨ s≤s (≤length-remove' a x a∈'x) ⟩
        length (b ∷ x)
      ≤-∎

----------------------------------
  
  once-contain→minimal : (list : List A)
                → (once : (a₁ : A) → a₁ ∈ list → a₁ ∈₁ list)
                → (l : List A)
                → (contain : (b : A) → (b ∈' list) → b ∈' l)
                → length list ≤ length l       
  once-contain→minimal [] once l contain = z≤n
  once-contain→minimal (a ∷ list) once l contain = 
      ≤-begin
        length (a ∷ list)
      ≤⟨ ≤-reflexive (length-∷ a list) ⟩
        1 + (length list)
      ≤⟨ s≤s (once-contain→minimal list once' l' contain') ⟩
        1 + length (remove' a l a∈'l) 
      ≤⟨ ≤length-remove' a l a∈'l ⟩
        length l
      ≤-∎
      where
        a∈'l = contain a (here')
        l' = remove' a l a∈'l
        once' = once-∷ a list once
        contain' = contain-∷ a list once l contain
    
  once-exist'→minimal : (list : List A) 
                      → (once : (a₁ : A) → a₁ ∈ list → a₁ ∈₁ list)
                        (l : List A)
                      → (exist' : (aₑ : A) → aₑ ∈ l)
                      → length list ≤ length l
  once-exist'→minimal list once l exist' = once-contain→minimal list once l λ b _ → (∈⇒∈' (exist' b))                


module _ where

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


  infix 0 _≃_
  record _≃_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      to   : A → B
      from : B → A
      from∘to : ∀ (x : A) → from (to x) ≡ x
      to∘from : ∀ (y : B) → to (from y) ≡ y
  open _≃_ public



  open import Data.Nat.Base


  record FinSet {i : Level} : Set (lsuc i) where
    field
      Carrier : Set i
      list : List Carrier
      exist : (aₑ : Carrier) → aₑ ∈ list
      -- minimal : (l : List Carrier) → ((aₘ : Carrier) → aₘ ∈ l) → length list ≤ length l
      once : (a₁ : Carrier) → a₁ ∈ list → a₁ ∈₁ list
  open FinSet public
                
                 