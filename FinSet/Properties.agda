{-# OPTIONS --allow-unsolved-metas #-}
module FinSet.Properties where
    

-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive; ≤-refl; +-mono-≤; +-assoc; +-comm)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym)


open import Agda.Primitive
open import Data.List.Base public
open import Data.List.Properties
open import Data.Empty public

open import FinSet.Membership

module _ {i : Level} {A : Set i} where
  ∈⇒≡ : ∀ {a b : A} → a ∈ [ b ] → a ≡ b 
  ∈⇒≡ here = refl

  ≡⇒∈ : ∀ {a b : A} → a ≡ b → a ∈ [ b ] 
  ≡⇒∈ refl = here

  -- ∈ ---

  ∈x⇒∈xy : ∀ {a : A} {x y : List A}
            → (a∈x : a ∈ x)
            → (a ∈ (x ++ y))
  ∈x⇒∈xy here = here
  ∈x⇒∈xy (there a∈x) = there (∈x⇒∈xy a∈x)

  ∈y⇒∈xy : ∀ {a : A} {x y : List A}
            → (a∈y : a ∈ y)
            → (a ∈ (x ++ y))
  ∈y⇒∈xy {x = []} a∈y = a∈y
  ∈y⇒∈xy {x = x ∷ x₁} a∈y = there (∈y⇒∈xy a∈y) 

  -- ∉ ---
  
  ∉-ept : ∀ {a : A} 
          → a ∉ []
  ∉-ept {a} ()

  ∉⇒∉h : ∀ {a b : A} {x : List A} → a ∉ (b ∷ x) → a ∉ [ b ]
  ∉⇒∉h a∉bx a∈b = a∉bx (∈x⇒∈xy a∈b)
  
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

  -- ∈₁ ---

  ∈₁⇒∈ : ∀ {a : A} {x : List A} 
          → a ∈₁ x 
          → a ∈ x
  ∈₁⇒∈ (here₁ a∉y) = here
  ∈₁⇒∈ (there₁ a∉x x) = there (∈₁⇒∈ x)

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

  ∈₁xy∈x⇒∉y : ∀ {a : A} {x y : List A}
                → (a∈₁xy : a ∈₁ (x ++ y))
                → (a∈x : a ∈ x)
                → (a ∉ y) 
  ∈₁xy∈x⇒∉y {x = .(_ ∷ _)} (here₁ a∉xy) here a∈y = a∉xy (∈y⇒∈xy a∈y)
  ∈₁xy∈x⇒∉y {x = .(_ ∷ _)} (there₁ a∉b a∈₁xy) here a∈y = a∉b here
  ∈₁xy∈x⇒∉y {x = .(_ ∷ _)} (here₁ a∉xy) (there a∈x) a∈y = a∉xy (∈y⇒∈xy a∈y)
  ∈₁xy∈x⇒∉y {x = .(_ ∷ _)} (there₁ a∉b a∈₁xy) (there a∈x) = ∈₁xy∈x⇒∉y a∈₁xy a∈x

  ∈₁xy∈y⇒∉x : ∀ {a : A} {x y : List A}
                → (a∈₁xy : a ∈₁ (x ++ y))
                → (a∈y : a ∈ y)
                → (a ∉ x) 
  ∈₁xy∈y⇒∉x a∈₁xy a∈y a∈x = ∈₁xy∈x⇒∉y a∈₁xy a∈x a∈y

  ∈₁xy∉x⇒∈₁y : ∀ {a : A} {x y : List A}
                → (a∈₁xy : a ∈₁ (x ++ y))
                → (a∉x : a ∉ x) 
                → (a ∈₁ y)
  ∈₁xy∉x⇒∈₁y {x = []} a∈₁xy a∉x = a∈₁xy
  ∈₁xy∉x⇒∈₁y {x = x ∷ x₁} (here₁ a∉x₁) a∉x = ⊥-elim (a∉x here)
  ∈₁xy∉x⇒∈₁y {x = x ∷ x₁} (there₁ a∉b a∈₁xy) a∉x = ∈₁xy∉x⇒∈₁y a∈₁xy (∉⇒∉t a∉x)

--  ∈₁xy∉y⇒∈₁x : ∀ {a : A} {x y : List A}
--                → (a∈₁xy : a ∈₁ (x ++ y))
--                → (a∉y : a ∉ y) 
--                → (a ∈₁ x)
--  ∈₁xy∉y⇒∈₁x {x = []} a∈₁xy a∉y = ⊥-elim (a∉y (∈₁⇒∈ a∈₁xy))
--  ∈₁xy∉y⇒∈₁x {x = x ∷ x₁} (here₁ a∉x) a∉y = here₁ {!   !}
--  ∈₁xy∉y⇒∈₁x {x = x ∷ x₁} (there₁ a∉b a∈₁xy) a∉y = {!   !}


-- once-∷ ----------------------------------------------------------------------------------

  once-∷  : {b : A} {x : List A}
          → (Once (b ∷ x))
          → (Once x)
  once-∷ {b} {x} once a a∈x = ∈₁xy∉x⇒∈₁y a∈₁bx a∉b
    where
      a∈₁bx : a ∈₁ (b ∷ x)
      a∈₁bx = once a (there a∈x)
      a∉b : a ∉ [ b ]
      a∉b = ∈₁xy∈y⇒∉x a∈₁bx a∈x


  -- contain-∷ -------------------------------------------------------------------------------------------
  
  contain-∷ : {b : A} {list l : List A}
            → (once : Once (b ∷ list))
            → (contain : Contain (b ∷ list) l)
            → (Contain list (remove b l (contain b here)))
  contain-∷ {b} {list} {[]} once contain c c∈list = ⊥-elim (∉-ept (contain c (there c∈list)))
  contain-∷ {b} {list} {b' ∷ l} once contain c c∈list = ∈-remove b∈l c∈b'l (∈₁xy∈y⇒∉x (once c c∈blist) c∈list)
    where
      c∈blist : c ∈ (b ∷ list)
      c∈blist = there c∈list
      b∈l = contain b here
      c∈b'l : c ∈ (b' ∷ l)
      c∈b'l = contain c (c∈blist)

      
 -- length --------------------------------

  open import Data.Nat.Base

  length-remove : ∀ (a : A) → (l : List A) → (a∈l : a ∈ l) → 1 + length (remove a l a∈l) ≡ length l
  length-remove a .(a ∷ l) (here {x = l}) = refl
  length-remove a .(b ∷ l) (there {b = b} {x = l} a∈l) = cong (1 +_) (length-remove a l a∈l)

----------------------------------
  
  once-contain→minimal : {list l : List A}
                      → (Once list)
                      → (Contain list l)
                      → length list ≤ length l       
  once-contain→minimal {[]} {l} once contain = z≤n
  once-contain→minimal {a ∷ list} {l} once contain = 
      ≤-begin
        length (a ∷ list)
      ≤⟨ ≤-refl ⟩
        1 + (length list)
      ≤⟨ s≤s (once-contain→minimal once' contain') ⟩
        1 + length (remove a l a∈l) 
      ≤⟨ ≤-reflexive (length-remove a l a∈l) ⟩
        length l
      ≤-∎
      where
        a∈l = contain a (here)
        l' = remove a l a∈l
        once' = once-∷ once
        contain' = contain-∷ once contain
    
  once-exist'→minimal : {list l : List A} 
                      → (Once list)
                      → (Exist l)
                      → length list ≤ length l
  once-exist'→minimal {list} {l} once exist' = once-contain→minimal once λ b _ → (exist' b)                

---------------------------------------------------------------------------------------------
module _ {i i' : Level} {A : Set i} {B : Set i'} where 

  inject-∈    : (l : List A) (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (a : A) → (fa∈fl :  f a ∈ map f l) → (a ∈ l)
  inject-∈ (x ∷ []) f inject a fa∈fl = ≡⇒∈ (inject a x (∈⇒≡ fa∈fl))
  inject-∈ (x ∷ x₁ ∷ l) f inject a fa∈fl = {!   !}

  inject-∈'    : {l : List A} (f : A → B)
              → (inject : (a a' : A) → f a ≡ f a' → a ≡ a')
              → (a : A) → (fa∈fl :  f a ∈ map f l) → (a ∈ l)
  inject-∈' {l@(x ∷ l')} f inject a fa∈fl with map f l | fa∈fl
  ... | []      | ()
  ... | _ ∷ _   | here = ∈x⇒∈xy {x = [ x ]} (≡⇒∈ (inject a x ((∈⇒≡ {!   !})))) -- (≡⇒∈ (inject a x (∈⇒≡ here)))
  ... | _ ∷ _   | there fa∈fl' = ∈y⇒∈xy (inject-∈' {l = l'} f inject a {! fa∈fl'  !})

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
  ... | _            | there₁ a∉a _  = ⊥-elim (a∉a here)  
  ... | here         | here₁  a∉l    = here₁ (inject-∉ l f inject a a∉l)  
  ... | there b∈fl   | here₁  a∉l    = there₁ b∉fa (inject-once l f inject (once-∷ once) b b∈fl)  
    where
      b∉fa : (b ∈ (f a ∷ [])) → ⊥
      b∉fa here = a∉l (inject-∈ l f inject a b∈fl)
          
    



module _ where

  congm : ∀ {i : Level} {A B : Set i} {a : A} {l : List A} → (f : A → B) → (a∈l : a ∈ l) → (f a) ∈ (map f l)
  congm f here = here
  congm f (there a∈l) = there (congm f a∈l) 

  substm : ∀ {i : Level} {A : Set i} {a aa : A} {x : List A} → a ≡ aa → (a∈x : a ∈ x) → aa ∈ x
  substm refl a∈x = a∈x

   
   