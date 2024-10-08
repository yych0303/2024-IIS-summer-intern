{-# OPTIONS --allow-unsolved-metas #-}
module Embedding.Emb.embFinSetN where


-- import Reasoning ≡ ≤ ----------------------------------
import Data.Nat.Properties as Np
open Np.≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to _≤-∎) hiding (step-≡-∣; step-≡-⟩)
open Np using (≤-reflexive)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)
open Eq using (cong₂)-- _≡_; refl; cong; cong-app; trans; subst; sym; 



open import Level using (Level)

open import Data.Nat.Base -- using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-reflexive )
open import Data.List using (List; map)
open import Data.List.Properties

-- Files

open import Embedding.Base public
open import Ring.Data.RingN
open import Ring.Data.RingFinSet


module _ where -- embFinSetN
  
  private
    
    length-≤ : ∀ {i : Level} {X Y : FinSet {i}} (P : Carrier X ≃ Carrier Y) → length (list X) ≤ length (list Y)
    length-≤ {X = X} {Y = Y} P = ≤-trans (minimal (once X) enum-fy) ( ≤-reflexive  (length-map (from P) (list Y)) )
      where
        fy : List (Carrier X)
        fy = map (from P) (list Y)
    
        enum-fy : (a : Carrier X) → a ∈ fy
        enum-fy a = substm (from∘to P a) (congm (from P) (enum Y (to P a)))
    
        
    length-≥ : ∀ {i : Level} {X Y : FinSet {i}} (P : Carrier X ≃ Carrier Y) → length (list Y) ≤ length (list X)
    length-≥ {X = X} {Y = Y} P = ≤-trans (minimal (once Y) enum-tx) ( ≤-reflexive  (length-map (to P) (list X)) )
      where
        tx : List (Carrier Y)
        tx = map (to P) (list X)
    
        enum-tx : (b : Carrier Y) → b ∈ tx
        enum-tx b = substm (to∘from P b) (congm (to P) (enum X (from P b)))
        



    length-cart : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → (f : A → B → C) (xs  : List A) → (ys  : List B) → length (cartesianProductWith f xs ys ) ≡ length xs * length ys
    length-cart f [] ys = refl
    length-cart f (x ∷ xs) ys = 
        ≡-begin 
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
        ≡-∎
      
      
      --rewrite (length-++  (map (f x) ys) {cartesianProductWith f xs ys} ) | length-map (f x) ys  =  trans refl (trans {! cong (length ys +_) length-cart f xs ys  !} refl ) -- cong (length ys +_) length-cart f xs ys

  embFinSetN : Embedding ringFinSet ringℕ
  embFinSetN = record
    { EF = λ X → length (list X)                                       
    ; E0 = refl                                       
    ; E1 = refl                                       
    ; E+ = λ X Y → trans (length-++ (map inj₁ (list X)) {map inj₂ (list Y)}) (cong₂ _+_ (length-map inj₁ (list X)) (length-map inj₂ (list Y)))                              
    ; E* = λ X Y → length-cart _ (list X) (list Y)                                       
    ; Eh = {!   !}                                       
    ; Et = {!   !}                                        
    ; E~ = λ X Y P → ≤-antisym (length-≤ {X = X} {Y = Y} P) (length-≥ {X = X} {Y = Y} P)                                     
    }




module _ where -- Func N → FinSet

  open import Data.Fin using (Fin) renaming (suc to fsuc ; zero to fzero)
  -- open import Data.Fin.Properties
      
  open import Data.Empty using (⊥-elim)
  open import Agda.Primitive using (lzero)


  -- properties of list
  module _ {i : Level} {A : Set i} where
    
   

  private
    
    L : (n : ℕ) → List (Fin n)
    L zero = []
    L (suc n) = fzero ∷ map fsuc (L n)
    
    P : (n : ℕ) → (x : Fin n) → x ∈ L n
    P zero = λ ()
    P (suc n) fzero = here
    P (suc n) (fsuc x) = ∈y⇒∈xy (congm fsuc (P n x))


    O : ∀ (n : ℕ) → (a : Fin n) → a ∈ L n → a ∈₁ L n
    O (suc n) fzero a∈l = (here₁ 0∉mfl')
      where 
        0∉mfl' : (fzero ∈ map fsuc (L n)) → ⊥
        0∉mfl' () 
          
    O (suc n) (fsuc a) a∈l = there₁ sa∉0 fa∈₁mfl'  
      where
        sa∉0 : (fsuc a ∈ (fzero ∷ [])) → ⊥
        sa∉0 (there fa∈0) = ∉-ept fa∈0

        fa∈₁mfl' : fsuc a ∈₁ map fsuc (L n)
        fa∈₁mfl' = inject-once (L n) fsuc inject-fsuc (O n) (fsuc a) (∈xy∉x⇒∈y {x = [ fzero ]} a∈l sa∉0)
          where
            inject-fsuc : (x x₁ : Fin n) → (fsuc x ≡ fsuc x₁) → x ≡ x₁
            inject-fsuc x .x refl = refl
    

  F : ℕ → FinSet { lzero }
  F = λ n → record { Carrier = Fin n ; list = L n ; enum = P n ; once = O n }

  -- EFF : EF F n ≡ n
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open Embedding embFinSetN

  EFF : ∀ (n : ℕ) → EF (F n) ≡ n
  EFF zero = refl
  EFF (suc n) =  
    ≡-begin 
      EF (F (suc n))
    ≡⟨⟩
      length (L (suc n))
    ≡⟨⟩
      length (fzero ∷ map fsuc (L n))
    ≡⟨⟩
      suc (length (map fsuc (L n)))
    ≡⟨ cong suc (length-map fsuc ((L n))) ⟩
      suc (length (L n))
    ≡⟨ cong suc (EFF n) ⟩
      suc n
    ≡-∎
  
   