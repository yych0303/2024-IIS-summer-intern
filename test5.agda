
open import Ring.Data.RingFinSet



open import Ring.Base
open import Embedding.Emb.embFinSetN
open import Term.Base
open import Term.Auto


open Ring ringFinSet
open Embedding embFinSetN

open import Data.Nat.Base

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


S₃ S₄ : R
S₃ = F 3
S₄ = F 4

Q = (S₃ R+ S₄) ~ (S₄ R+ S₃)



T₃ = ` (F 3)
T₄ = ` (F 4)


pf1 : (S₃ R+ S₄) ~ (S₄ R+ S₃)
pf1 = record { to   = λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y} 
             ; from =  λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
             ; from∘to = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
             ; to∘from = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
             }


pf1' : 3 + 4 ≡ 4 + 3 
pf1' = 
  begin 
    3 + 4
  ≡⟨⟩
    EF (S₃) + EF (S₄)
  ≡⟨ sym (E+ S₃ S₄) ⟩
    EF (S₃ R+ S₄)
  ≡⟨ E~ (S₃ R+ S₄) (S₄ R+ S₃) pf1  ⟩
    EF (S₄ R+ S₃)
  ≡⟨ E+ S₄ S₃ ⟩
    EF (S₄) + EF (S₃)
  ≡⟨⟩
    4 + 3  
  ∎

pf1'' : 3 + 4 ≡ 4 + 3 
pf1'' = auto embFinSetN (` (F 3) `+ ` (F 4)) (` (F 4) `+ ` (F 3)) pf1






-- Fₙ + Fₘ ~ Fₘ + Fₙ = Sₙ ⊎ Sₘ ≃  Sₘ ⊎ Sₙ
combi-pf : (n m : ℕ) → ((F n) R+ (F m)) ~ ((F m) R+ (F n))
combi-pf n m = record { to   = λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y} 
                      ; from =  λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
                      ; from∘to = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                      ; to∘from = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                      }


algeb-pf : (n m : ℕ) → n + m ≡ m + n 
algeb-pf n m = 
  begin 
    n + m
  ≡⟨ sym (cong₂ _+_ (EFF n) (EFF m)) ⟩
    EF (F n) + EF (F m)
  ≡⟨ sym (E+ (F n) (F m)) ⟩
    EF ((F n) R+ (F m))
  ≡⟨ E~ ((F n) R+ (F m)) ((F m) R+ (F n)) (combi-pf n m)  ⟩
    EF ((F m) R+ (F n))
  ≡⟨ E+ (F m) (F n) ⟩
    EF (F m) + EF (F n)
  ≡⟨ cong₂ _+_ (EFF m) (EFF n) ⟩
    m + n  
  ∎

algeb-pf-auto : (n m : ℕ) → EF (F n) + EF (F m) ≡ EF (F m) + EF (F n)
algeb-pf-auto n m = auto embFinSetN (` (F n) `+ ` (F m)) (` (F m) `+ ` (F n)) (combi-pf n m) 



open import Data.Product

combi-pf2 : (n m l : ℕ) → ((F n) R* ((F m) R* (F l))) ~ (((F n) R* (F m)) R* (F l))
combi-pf2 n m l = record { to   = λ {(i , (j , k)) → ((i , j) , k)} 
                      ; from = λ {((i , j) , k) → (i , (j , k))}
                      ; from∘to = λ {(i , (j , k)) → refl}
                      ; to∘from = λ {((i , j) , k) → refl}
                      }




algeb-pf2 : (n m l : ℕ) → n * (m * l) ≡ (n * m) * l 
algeb-pf2 n m l = 
  begin 
    n * (m * l)
  ≡⟨ sym (cong (_* (m * l)) (EFF n)) ⟩
    EF (F n) * (m * l)
  ≡⟨ sym (cong (EF (F n) *_) (cong₂ _*_ (EFF m) (EFF l))) ⟩
    EF (F n) * (EF (F m) * EF (F l))
  ≡⟨ sym (cong (EF (F n) *_) (E* (F m) (F l))) ⟩
    EF (F n) * EF ((F m) R* (F l))
  ≡⟨ sym (E* (F n) ((F m) R* (F l))) ⟩
    EF ((F n) R* ((F m) R* (F l)))
  ≡⟨ E~ ((F n) R* ((F m) R* (F l))) (((F n) R* (F m)) R* (F l)) (combi-pf2 n m l)  ⟩
    EF (((F n) R* (F m)) R* (F l))
  ≡⟨ E* (((F n) R* (F m))) ((F l)) ⟩
    EF ((F n) R* (F m)) * EF (F l)
  ≡⟨ cong (_* EF (F l)) (E* (F n) (F m)) ⟩
    (EF (F n) * EF (F m)) * EF (F l)
  ≡⟨ cong (_* EF (F l)) (cong₂ _*_ (EFF n) (EFF m)) ⟩
    (n * m) * EF (F l)
  ≡⟨ cong ((n * m) *_) (EFF l) ⟩
    (n * m) * l
  ∎
