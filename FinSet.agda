{-# OPTIONS --allow-unsolved-metas #-}
module FinSet where
    
open import Agda.Primitive
open import Level


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans; subst; sym) public

open import Data.List.Base public
open import Data.List.Properties

infix 7 _∈_

data _∈_ {i : Level} {A : Set i} (a : A) : (x : List A) → Set i where
  here  : a ∈ [ a ]
  left  : ∀ {x y} → (a∈x : a ∈ x) → a ∈ (x ++ y)
  right : ∀ {x y} → (a∈y : a ∈ y) → a ∈ (x ++ y)

infix 7 _⊆_

data _⊆_ {i : Level} {A : Set i} : (x y : List A) → Set i where
  non  : ∀ {y} → [] ⊆ y 
  addl : ∀ {x y : List A} {a : A} → (x⊆y : x ⊆ y) → {!   !} 
  addr : {!   !}

    
congm : ∀ {i : Level} {A B : Set i} {b : B} {s : List B} → (f : B → A) → (b∈s : b ∈ s) → (f b) ∈ (map f s)
congm {b = b} {s = .([ b ])} f here = here
congm {b = b} {s = .(x ++ y)} f (left {x = x} {y = y} b∈x) =  subst (_∈_ (f b)) (sym (map-++ f x y)) (left {x = map f x} {y = map f y} (congm f b∈x))
congm {b = b} {s = .(x ++ y)} f (right {x = x} {y = y} b∈y) = subst (_∈_ (f b)) (sym (map-++ f x y)) (right {x = map f x} {y = map f y} (congm f b∈y))

substm : ∀ {i : Level} {A : Set i} {a aa : A} {x : List A} → a ≡ aa → (a∈x : a ∈ x) → aa ∈ x
substm refl a∈x = a∈x










open import Data.Nat

record FinSet {i : Level} : Set (lsuc i) where
  field
    Carrier : Set i
    list : List Carrier
    proof : (x : Carrier) → x ∈ list
    minimal : (l : List Carrier) → ((x : Carrier) → x ∈ l) → length list ≤ length l
open FinSet

