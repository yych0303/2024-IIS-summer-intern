

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
-- open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)

open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- open import Data.Unit using (⊤; tt)
-- open import Data.Empty using (⊥; ⊥-elim)
-- open import Function.Equivalence using (_⇔_)

```

## Fin

Goal (S ≃ T) ⇔ (N = M)


⟦_⟧ (n : ℕ) : Set
  zero : ⟦ suc n ⟧

_×_ (A B : Set) : Set
Σ[]
Π

#_ (A : Set) : ℕ




data ⟦_⟧ : ℕ → Set where
  Φ : ⟦ 0 ⟧
  S : {n : ℕ} → (s : ⟦ n ⟧) → ⟦ suc n ⟧


-- def ⨄ ­- × ／

data _! : ⟦_⟧ → Set where
  ⟦ 1 ⟧ : ⟦ 0 ⟧ !
  S ⟦ n ⟧ × (⟦ n ⟧ !) : {n : ℕ} → (S ⟦ n ⟧) !



-- #_ : (A : Set) → ℕ
-- # A = {!  !}

 
```agda

-- Num


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)



-- Definition of Fin
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)




-- Definition of Factorial
data Factorial : ℕ → Set where
  Φ! : {f : Fin 1} → Factorial 0
  ε! : {n : ℕ} → {f : Fin (suc n)} → Factorial n → Factorial (suc n)

-- Definition of  C
-- data Combin ℕ → ℕ → Set where


-- Comb

Ele = ℕ

data Comb : Set where
  Φ : Comb
  ε : {Ele} → Comb → Comb

unit = ε {_} Φ

-- Elements 
lookup : Ele → Comb → Bool
lookup x Φ = false
lookup x (ε {y} A) with x Data.Nat.≟ y
...                   | yes _ = true
...                   | no  _ = lookup x A

-- relation 



postulate
  ε-commute : ∀ {x y : Ele} {A : Comb} → (ε {x} (ε {y} A) ≡ ε {y} (ε {x} A)) 


_U_ : Comb → Comb → Comb
Φ U B = B
ε {x} A U B = ε {x} (A U B)

--  _-_ : Comb → Comb → Comb
--  Φ - B = Φ
--  A - Φ = A
--  ε A - ε B = A - B

_∙_ : Comb → Comb → Comb
Φ ∙ B = Φ
ε A ∙ B = B U (A ∙ B) 

-- _/_: Comb → Comb

Σ[x:_]_ : Comb → (Ele → Comb) → Comb
Σ[x: Φ ] F = Φ
Σ[x: ε {x} A ] F = (F x) U (Σ[x: A ] F) 

Π[x:_]_ : Comb → (Ele → Comb) → Comb
Π[x: Φ ] F = unit
Π[x: ε {x} A ] F = (F x) ∙ (Π[x: A ] F)

_! : Comb → Comb
Φ ! = unit
ε {x} A ! = ε {x} A ∙ (A !)





# : Comb → ℕ
# Φ = zero
# (ε A) = suc (# A)

-- propersitions
postulate
  _ : ∀ {A B : Comb} → # (A U B) ≡ # A + # B
  -- _ : ∀ {A B : Comb} → # (A - B) ≡ # A ∸ # B
  _ : ∀ {A B : Comb} → # (A ∙ B) ≡ # A * # B
  -- _ : ∀ {A B : Comb} → # (A / B) ≡ # A / # B
  _ : ∀ {A : Comb} {F : Ele → Comb} → # (Σ[x: A ] F) ≡ {!   !}
  _ : ∀ {A : Comb} {F : Ele → Comb} → # (Π[x: A ] F) ≡ {!   !}
  




-- create Comb 

⟦_⟧ : ℕ → Comb
⟦ zero ⟧ = Φ
⟦ suc n ⟧ = ε {suc n} ⟦ n ⟧






```



 



  
  