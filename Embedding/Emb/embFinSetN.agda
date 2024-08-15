{-# OPTIONS --allow-unsolved-metas #-}
module Embedding.Emb.embFinSetN where

open import Embedding.Base

open import Data.Nat.Base -- using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-reflexive )
open import Data.List using (List; map)


open import Relation.Binary.PropositionalEquality.Core using (cong₂)
open import Ring.Data.RingN
-- open import Ring.Data.RingSt
open import Ring.Data.RingFinSet

open import Data.List.Properties

open FinSet


open import Level

private
  length-≤ : ∀ {i : Level} {X Y : FinSet {i}} (P : Carrier X ≃ Carrier Y) → length (list X) ≤ length (list Y)
  length-≤ {X = X} {Y = Y} P = ≤-trans (minimal X fy proof-fy) ( ≤-reflexive  (length-map (from P) (list Y)) )
    where
      fy : List (Carrier X)
      fy = map (from P) (list Y)
  
      proof-fy : (a : Carrier X) → a ∈ fy
      proof-fy a = substm (from∘to P a) (congm (from P) (proof Y (to P a)))
  
      
  length-≥ : ∀ {i : Level} {X Y : FinSet {i}} (P : Carrier X ≃ Carrier Y) → length (list Y) ≤ length (list X)
  length-≥ {X = X} {Y = Y} P = ≤-trans (minimal Y tx proof-tx) ( ≤-reflexive  (length-map (to P) (list X)) )
    where
      tx : List (Carrier Y)
      tx = map (to P) (list X)
  
      proof-tx : (b : Carrier Y) → b ∈ tx
      proof-tx b = substm (to∘from P b) (congm (to P) (proof X (from P b)))
  

  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning


  length-cart : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → (f : A → B → C) (xs  : List A) → (ys  : List B) → length (cartesianProductWith f xs ys ) ≡ length xs * length ys
  length-cart f [] ys = refl
  length-cart f (x ∷ xs) ys = 
      begin 
        length (cartesianProductWith f (x ∷ xs) ys)
      ≡⟨⟩
        length (map (f x) ys ++ cartesianProductWith f xs ys)
      ≡⟨ length-++ (map (f x) ys) {cartesianProductWith f xs ys} ⟩
        length (map (f x) ys) + length (cartesianProductWith f xs ys)
      ≡⟨ cong (_+ length (cartesianProductWith f xs ys)) (length-map (f x) ys) ⟩
        length ys + length (cartesianProductWith f xs ys)
      ≡⟨ cong (length ys +_) (length-cart f xs ys) ⟩
        length ys + length xs * length ys
      ≡⟨⟩
        (1 + length xs) * length ys
      ≡⟨⟩
        length (x ∷ xs) * length ys
      ∎
    
    
    --rewrite (length-++  (map (f x) ys) {cartesianProductWith f xs ys} ) | length-map (f x) ys  =  trans refl (trans {! cong (length ys +_) length-cart f xs ys  !} refl ) -- cong (length ys +_) length-cart f xs ys

embFinSetN : Embedding ringFinSet ringℕ
embFinSetN = record
  { EF = λ X → length (list X)                                       
  ; E0 = refl                                       
  ; E1 = refl                                       
  ; Eh = {!   !}                                       
  ; Et = {!   !}                                        
  ; E+ = λ X Y → trans (length-++ (map inj₁ (list X)) {map inj₂ (list Y)}) (cong₂ _+_ (length-map inj₁ (list X)) (length-map inj₂ (list Y)))                              
  ; E* = λ X Y → length-cart _ (list X) (list Y)                                       
  ; E~ = λ X Y P → ≤-antisym (length-≤ {X = X} {Y = Y} P) (length-≥ {X = X} {Y = Y} P)                                     
  }


 