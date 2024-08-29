
open import Ring.Data.RingFinSet



open import Ring.Base

open Ring ringFinSet

open import Data.Nat.Base

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Embedding.Emb.embFinSetN
open Embedding embFinSetN

S₃ S₄ : R
S₃ = F 3
S₄ = F 4

Q = (S₃ R+ S₄) ~ (S₄ R+ S₃)

pf1 : (S₃ R+ S₄) ~ (S₄ R+ S₃)
pf1 = {!   !}


Q' = 3 + 4 ≡ 4 + 3


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

lemma-1 : ∀ (m : ℕ) → m + zero ≡ m
lemma-1 zero = refl
lemma-1 (suc m) rewrite lemma-1 m = refl

lemma-2 : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
lemma-2 zero n = refl
lemma-2 (suc m) n rewrite lemma-2 m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite lemma-1 m = refl
+-comm m (suc n) rewrite lemma-2 m n | +-comm m n = refl

lemma-1 : ∀ (m : ℕ) → m + zero ≡ m
lemma-1 zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
lemma-1 (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (lemma-1 m) ⟩
    suc m
  ∎
lemma-2 : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
lemma-2 zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
lemma-2 (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (lemma-2 m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ lemma-1 m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ lemma-2 m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)

*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


Here’s how to rewrite the *-assoc proof using the reasoning style (begin...∎) instead of rewrite:


*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
  ≡⟨⟩
    zero * p
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n + m * n) * p
  ≡⟨ *-assoc m n p ⟩
    n * p + (m * n) * p
  ≡⟨⟩
    suc m * (n * p)
  ∎