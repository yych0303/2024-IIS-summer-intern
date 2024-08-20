{-# OPTIONS --allow-unsolved-metas #-}
module FinSet where
    
open import Agda.Primitive
open import Level
open import Data.Empty using (⊥-elim) public

-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive; ≤-refl; +-mono-≤; +-assoc; +-comm)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym)


open import Data.List.Base public
open import Data.List.Properties

open import Relation.Nullary using (Dec; ¬_) public

open import Data.Sum using (_⊎_) public
open import Data.Empty public



module _ {i : Level} {A : Set i} where

  infix 7 _∈_
  infix 7 _∉_
  infix 7 _∈₁_


 
  data _∈_ (a : A) : (x : List A) → Set i where
    here  : ∀ {x} → a ∈ (a ∷ x)
    there : ∀ {b} {x} → (a∈x : a ∈ x) → a ∈ (b ∷ x)
    
  _∉_ : (a : A) → (x : List A) → Set i
  a ∉ x = ¬ (a ∈ x)
  
  data _∈₁_ (a : A) : (x : List A) → Set i where
    here₁  : ∀ {x} → (a∉x : a ∉ x) → a ∈₁ (a ∷ x) 
    there₁ : ∀ {b x} → (a∉b : a ∉ [ b ]) → (a∈₁x : a ∈₁ x) → a ∈₁ (b ∷ x)





  ∉-ept : ∀ {a : A} → a ∉ []
  ∉-ept {a} ()


  ∈₁⇒∈ : ∀ {a : A} {x : List A} → a ∈₁ x → a ∈ x
  ∈₁⇒∈ (here₁ a∉y) = here
  ∈₁⇒∈ (there₁ a∉x x) = there (∈₁⇒∈ x)

--  ∉∈⇒∈t : ∀ {a b : A} {x : List A}
--            → (a∉b : a ∉ (b ∷ []))
--            → (a∈bx : a ∈ (b ∷ x))
--            → (a ∈ x)
--  ∉∈⇒∈t a∉b here = ⊥-elim (a∉b here)
--  ∉∈⇒∈t a∉b (there a∈bx) = a∈bx


  ∈x⇒∈xy : ∀ {a : A} {x y : List A}
          → (a∈x : a ∈ x)
          → (a ∈ (x ++ y))
  ∈x⇒∈xy here = here
  ∈x⇒∈xy (there a∈x) = there (∈x⇒∈xy a∈x)

  ∉⇒∉h : ∀ {a b : A} {x : List A} → a ∉ (b ∷ x) → a ∉ [ b ]
  ∉⇒∉h a∉bx a∈b = a∉bx (∈x⇒∈xy a∈b)
  
  ∈y⇒∈xy : ∀ {a : A} {x y : List A}
          → (a∈y : a ∈ y)
          → (a ∈ (x ++ y))
  ∈y⇒∈xy {x = []} a∈y = a∈y
  ∈y⇒∈xy {x = x ∷ x₁} a∈y = there (∈y⇒∈xy a∈y) 


  ∉⇒∉t : ∀ {a b : A} {x : List A}
        → (a∉bx : a ∉ (b ∷ x))
        → (a ∉ x)
  ∉⇒∉t {b = b} a∉bx a∈x = a∉bx (there a∈x)
  
  ∉∉⇒∉ : ∀ {a : A} {x y : List A}
        → (a∉x : a ∉ x)
        → (a∉y : a ∉ y)
        → (a ∉ (x ++ y))
  ∉∉⇒∉ {x = []} a∉x a∉y a∈xy = a∉y a∈xy
  ∉∉⇒∉ {x = x ∷ x'} a∉x a∉y a∈xy with a∈xy
  ... | there a∈xy'  = ∉∉⇒∉ {x = x'} (∉⇒∉t a∉x) a∉y a∈xy'
  ... | here         = a∉x here

  ∈₁x∉y⇒∈₁xy : ∀ {a : A} {x y : List A}
              → (a∈₁x : a ∈₁ x)
              → (a∉y : a ∉ y)
              → (a ∈₁ (x ++ y))
  ∈₁x∉y⇒∈₁xy (here₁ a∉y₁) a∉y = here₁ (∉∉⇒∉ a∉y₁ a∉y)
  ∈₁x∉y⇒∈₁xy (there₁ a∉x a∈₁x) a∉y = there₁ a∉x (∈₁x∉y⇒∈₁xy a∈₁x a∉y)

  ∉x∈₁y⇒∈₁xy : ∀ {a : A} {x y : List A}
              → (a∉x : a ∉ x)
              → (a∈₁y : a ∈₁ y)
              → (a ∈₁ (x ++ y))
  ∉x∈₁y⇒∈₁xy {x = []} a∉x a∉y = a∉y
  ∉x∈₁y⇒∈₁xy {x = x ∷ x₁} a∉x a∉y = there₁ (∉⇒∉h a∉x) (∉x∈₁y⇒∈₁xy (∉⇒∉t a∉x) a∉y)

  ∈xy∉y⇒∈x : ∀ {a : A} {x y : List A}
              → (a∈xy : a ∈ (x ++ y))
              → (a∉y : a ∉ y)
              → (a ∈ x)
  ∈xy∉y⇒∈x {x = []} a∈xy a∉y = ⊥-elim (a∉y a∈xy)
  ∈xy∉y⇒∈x {x = x ∷ x₁} here a∉y = here
  ∈xy∉y⇒∈x {x = x ∷ x₁} (there a∈xy) a∉y = there (∈xy∉y⇒∈x a∈xy a∉y)
 
  ∈xy∉x⇒∈y : ∀ {a : A} {x y : List A}
              → (a∈xy : a ∈ (x ++ y))
              → (a∉x : a ∉ x)
              → (a ∈ y)
  ∈xy∉x⇒∈y {x = []} a∈xy a∉x = a∈xy
  ∈xy∉x⇒∈y {x = x ∷ x₁} here a∉x = ⊥-elim (a∉x here)
  ∈xy∉x⇒∈y {x = x ∷ x₁} (there a∈xy) a∉x = ∈xy∉x⇒∈y a∈xy (∉⇒∉t a∉x)

  ---
  ∈⇒≡ : ∀ {a b : A} → a ∈ [ b ] → a ≡ b 
  ∈⇒≡ here = refl

  ≡⇒∈ : ∀ {a b : A} → a ≡ b → a ∈ [ b ] 
  ≡⇒∈ refl = here

  
  --nonept : ∀ {a : A} → (x : List A) → a ∈ x → ¬ (x ≡ []) 
  --nonept [] ()
  --nonept (x ∷ xs) _ = λ ()

  remove : (a : A) → (x : List A) → (a∈x : a ∈ x) → List A
  remove a .(a ∷ x) (here {x = x}) = x
  remove a .(b ∷ x) (there {b = b} {x = x} a∈x) = b ∷ remove a x a∈x

  
  ∈-remove  : ∀ {b c : A} {l : List A}
              → (b∈l : b ∈ l)
              → (c∈l : c ∈ l)
              → (c∉b : c ∉ [ b ])
              → (c ∈ (remove b l b∈l))
  ∈-remove here here c∉b = ⊥-elim (c∉b here)
  ∈-remove here (there c∈l) c∉b = c∈l
  ∈-remove (there b∈l) here c∉b = here
  ∈-remove (there b∈l) (there c∈l) c∉b = there (∈-remove b∈l c∈l c∉b)

--------------------------------------------

  


  notfst : ∀ {a b : A} {x : List A}
        → (a∈₁bx : a ∈₁ (b ∷ x))
        → (a∈x : a ∈ x)
        → (a ∉ [ b ]) 
  notfst (here₁ a∉x) a∈x a∈b = a∉x a∈x
  notfst (there₁ a∉b _) a∈x a∈b = a∉b a∈b




  once-∷  : (b : A) (x : List A)
          → (once : (a₁ : A) → a₁ ∈ (b ∷ x) → a₁ ∈₁ (b ∷ x))
          → ((a : A) → a ∈ x → a ∈₁ x)
  once-∷ b x once a a∈x = ∈₁-∷ {a = a} {b = b} a∉b a∈₁bx
    where
      a∈₁bx : a ∈₁ (b ∷ x)
      a∈₁bx = once a (there a∈x)
      a∉b : a ∉ [ b ]
      a∉b = notfst a∈₁bx a∈x

      ∈₁-∷ : ∀ {a b : A} {x : List A}
            → (a∉b : a ∉ [ b ]) 
            → (a∈₁bx : a ∈₁ (b ∷ x))
            → (a ∈₁ x)
      ∈₁-∷ a∉b (here₁ _) = ⊥-elim (a∉b here)
      ∈₁-∷ a∉b (there₁ _ a∈₁x) = a∈₁x

  ---------------------------------------------------------------------------------------------
  

  contain-∷ : (b : A) → (list : List A)
            → (once : (a₁ : A) → a₁ ∈ (b ∷ list) → a₁ ∈₁ (b ∷ list))
            → (l : List A)
            → (contain : (a : A) → (a ∈ (b ∷ list)) → a ∈ l)
            → ((c : A) → (c ∈ list) → c ∈ (remove b l (contain b here)))
  contain-∷ b list once [] contain c c∈list = ⊥-elim (∉-ept (contain c (there c∈list)))
  contain-∷ b list once (b' ∷ l) contain c c∈list = ∈-remove b∈l c∈b'l (notfst (once c c∈blist) c∈list)
    where
      c∈blist : c ∈ (b ∷ list)
      c∈blist = there c∈list
      b∈l = contain b here
      c∈b'l : c ∈ (b' ∷ l)
      c∈b'l = contain c (c∈blist)

      
 ----------------------------------

  open import Data.Nat.Base
  
  length-∷ : ∀ (x : A) → (xs : List A) → length (x ∷ xs) ≡ 1 + (length xs)
  length-∷ _ _ = refl

  ≤length-remove : ∀ (a : A) → (x : List A) → (a∈x : a ∈ x) → 1 + length (remove a x a∈x) ≤ length x
  ≤length-remove a .(a ∷ x) (here {x = x}) = 
      ≤-begin
        1 + length (x)
      ≤⟨ ≤-reflexive (sym (length-∷ a x)) ⟩
        length (a ∷ x)
      ≤-∎
  ≤length-remove a .(b ∷ x) (there {b = b} {x = x} a∈x) =
      ≤-begin
        1 + length (b ∷ (remove a x a∈x))
      ≤⟨ s≤s (≤length-remove a x a∈x) ⟩
        length (b ∷ x)
      ≤-∎

----------------------------------
  
  once-contain→minimal : (list : List A)
                → (once : (a₁ : A) → a₁ ∈ list → a₁ ∈₁ list)
                → (l : List A)
                → (contain : (b : A) → (b ∈ list) → b ∈ l)
                → length list ≤ length l       
  once-contain→minimal [] once l contain = z≤n
  once-contain→minimal (a ∷ list) once l contain = 
      ≤-begin
        length (a ∷ list)
      ≤⟨ ≤-reflexive (length-∷ a list) ⟩
        1 + (length list)
      ≤⟨ s≤s (once-contain→minimal list once' l' contain') ⟩
        1 + length (remove a l a∈l) 
      ≤⟨ ≤length-remove a l a∈l ⟩
        length l
      ≤-∎
      where
        a∈l = contain a (here)
        l' = remove a l a∈l
        once' = once-∷ a list once
        contain' = contain-∷ a list once l contain
    
  once-exist'→minimal : {list l : List A} 
                      → (once : (a₁ : A) → a₁ ∈ list → a₁ ∈₁ list)
                      → (exist' : (aₑ : A) → aₑ ∈ l)
                      → length list ≤ length l
  once-exist'→minimal {list} {l} once exist' = once-contain→minimal list once l λ b _ → (exist' b)                

---------------------------------------------------------------------------------------------
module _ {i i' : Level} {A : Set i} {B : Set i'} where 
  open import Data.Product using (Σ-syntax; _,_)

--  preimg : (l : List A) (f : A → B)
--           → (inject : (a a' : A) → f a ≡ f a' → a ≡ a)
--           → (b : B) → (b∈fl : b ∈ (map f l)) → Σ[ a ∈ A ] Σ[ a∈l ∈ (a ∈ l) ] (f a ≡ b)
--  preimg = {!   !}
--

  inject-∈    : (l : List A) (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (a : A) → (fa∈fl :  f a ∈ map f l) → (a ∈ l)
  inject-∈ (x ∷ []) f inject a fa∈fl = ≡⇒∈ (inject a x (∈⇒≡ fa∈fl))
  inject-∈ (x ∷ x₁ ∷ l) f inject a fa∈fl = {!   !}

  inject-∈'    : {l : List A} (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (a : A) → (fa∈fl :  f a ∈ map f l) → (a ∈ l)
  inject-∈' f inject a fa∈fl = {! fa∈fl  !}

  inject-∉    : (l : List A) (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (a : A) → (a∉l :  a ∉ l) → (f a ∉ (map f l))
  inject-∉ l f inject a a∉l fa∈fl = a∉l (inject-∈ l f inject a fa∈fl)

  inject-once : (l : List A) (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (once : (a₁ : A) → a₁ ∈ l → a₁ ∈₁ l)
              → ((b : B) → b ∈ (map f l) → b ∈₁ (map f l))
  inject-once [] _ _ _ _ b∈fl = ⊥-elim (∉-ept b∈fl)
  inject-once (a ∷ l) f inject once b b∈fl with b∈fl | once a here
  ... | _               | there₁ a∉a _  = ⊥-elim (a∉a here)  
  ... | here           | here₁  a∉l    = here₁ (inject-∉ l f inject a a∉l)  
  ... | there b∈fl   | here₁  a∉l    = there₁ b∉fa (inject-once l f inject (once-∷ a l once) b b∈fl)  
    where
      b∉fa : (b ∈ (f a ∷ [])) → ⊥
      b∉fa here = a∉l (inject-∈ l f inject a b∈fl)
          
    



module _ where

  congm : ∀ {i : Level} {A B : Set i} {a : A} {l : List A} → (f : A → B) → (a∈l : a ∈ l) → (f a) ∈ (map f l)
  congm f here = here
  congm f (there a∈l) = there (congm f a∈l) 

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
      once : (a₁ : Carrier) → a₁ ∈ list → a₁ ∈₁ list
  open FinSet public
                    