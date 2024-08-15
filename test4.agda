
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




pf2 : (n m : ℕ) → ((F n) R+ (F m)) ~ ((F m) R+ (F n))
pf2 = {!   !}


pf2' : (n m : ℕ) → n + m ≡ m + n 
pf2' n m = 
  begin 
    n + m
  ≡⟨ sym (cong₂ _+_ (EFF n) (EFF m)) ⟩
    EF (F n) + EF (F m)
  ≡⟨ sym (E+ (F n) (F m)) ⟩
    EF ((F n) R+ (F m))
  ≡⟨ E~ ((F n) R+ (F m)) ((F m) R+ (F n)) (pf2 n m)  ⟩
    EF ((F m) R+ (F n))
  ≡⟨ E+ (F m) (F n) ⟩
    EF (F m) + EF (F n)
  ≡⟨ cong₂ _+_ (EFF m) (EFF n) ⟩
    m + n  
  ∎

