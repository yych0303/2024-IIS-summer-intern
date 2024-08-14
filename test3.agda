open import Embedding.Base

open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; ≤-reflexive )
open import Data.List using (List; map)


open import Relation.Binary.PropositionalEquality.Core using (cong₂)
open import Ring.Data.RingN
-- open import Ring.Data.RingSt
open import Ring.Data.RingKu

open import Data.List.Properties

open FinSet


open import Level

private
  length-≤ : ∀ {i : Level} {x y : FinSet {i}} (p : Carrier x ≃ Carrier y) → length (list x) ≤ length (list y)
  length-≤ {x = x} {y = y} p = ≤-trans (minimal x fy proof-fy) ( ≤-reflexive  (length-map (from p) (list y)) )
    where
      fy : List (Carrier x)
      fy = map (from p) (list y)
  
      proof-fy : (a : Carrier x) → a ∈ fy
      proof-fy a = substm (from∘to p a) (congm (from p) (proof y (to p a)))
  
      
  length-≥ : ∀ {i : Level} {x y : FinSet {i}} (p : Carrier x ≃ Carrier y) → length (list y) ≤ length (list x)
  length-≥ {x = x} {y = y} p = ≤-trans (minimal y tx proof-tx) ( ≤-reflexive  (length-map (to p) (list x)) )
    where
      tx : List (Carrier y)
      tx = map (to p) (list x)
  
      proof-tx : (b : Carrier y) → b ∈ tx
      proof-tx b = substm (to∘from p b) (congm (to p) (proof x (from p b)))
  
  length-eq : ∀ {i : Level} {x y : FinSet {i}} (p : Carrier x ≃ Carrier y) → length (list x) ≡ length (list y)
  length-eq {x = x} {y = y} p = ≤-antisym (length-≤ {x = x} {y = y} p) (length-≥ {x = x} {y = y} p)
      
  

embTN : Embedding ringType ringℕ
embTN = record
  { EF = λ x → length (list x)                                       
  ; E0 = refl                                       
  ; E1 = refl                                       
  ; Eh = {!   !}                                       
  ; Et = {!   !}                                        
  ; E+ = λ x y → trans (length-++ (map inj₁ (list x)) {map inj₂ (list y)}) (cong₂ _+_ (length-map inj₁ (list x)) (length-map inj₂ (list y)))                              
  ; E* = {!   !}                                       
  ; E~ = λ x y p → ≤-antisym (length-≤ {x = x} {y = y} p) (length-≥ {x = x} {y = y} p)                                     
  }


