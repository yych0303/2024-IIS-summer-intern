## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
open import Relation.Nullary using (¬_; Dec; yes; no)
-- open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)

open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

open import Agda.Builtin.Sigma

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Equivalence using (_⇔_)



Type = Set

```
## Goal

Example:

C n , k = Σ [n] (λ i → C (i-1) (k-1))



Goal 

(S ≃ T) ⇔ (N = M)

1. type of combination
2. 


```agda

-- Num


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)

combination : ℕ → ℕ → ℕ
combination _ 0 = 1
combination 0 _ = 0
combination (suc i) (suc j) = combination i j + combination i (suc j) 




-- Comb ------------------------------

{-

Ele = ℕ

data Comb : Type where
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



-- # ---------------------------

# : Comb → ℕ
# Φ = zero
# (ε A) = suc (# A)

-- propersitions
postulate
  _ : ∀ {A B : Comb} → # (A U B) ≡ # A + # B
  -- _ : ∀ {A B : Comb} → # (A - B) ≡ # A ∸ # B
  _ : ∀ {A B : Comb} → # (A ∙ B) ≡ # A * # B
  -- _ : ∀ {A B : Comb} → # (A / B) ≡ # A / # B
  -- _ : ∀ {A : Comb} {F : Ele → Comb} → # (Σ[x: A ] F) ≡ {!   !}
  -- _ : ∀ {A : Comb} {F : Ele → Comb} → # (Π[x: A ] F) ≡ {!   !}
  




-- create Comb 

⟦_⟧ : ℕ → Comb
⟦ zero ⟧ = Φ
⟦ suc n ⟧ = ε {suc n} ⟦ n ⟧

-}
-- Pi Type --------------------------------------

Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ∶ A , b


-- Sg Type --------------------------------------
{-
data Σ {A : Type} (B : A → Type) : Type where
  _,_ : (x : A) (y : B x) → Σ {A} B
  
pr₁ : {A : Type} {B : A → Type} → Σ B → A
pr₁ (x , y) = x

pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
pr₂ (x , y) = y
-}



data _≣_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≣ x

infix 0 _≣_ 




-- ---------------------------------------

-- Definition of Fin
data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)


𝟘 = Fin 0
𝟙 = Fin 1
𝟚 = Fin 2





F→ℕ : ∀ {n} → Fin n → ℕ
F→ℕ zero = zero
F→ℕ (suc f) = suc (F→ℕ (f))

postulate
  f≲F : ∀ {n m : ℕ} 
    → n ≤ m
    ---------
    → Fin n ≲ Fin m




-- Pow n k
Pow : Type → Type → Type
Pow A B = Π x ∶ A , B


Fac : ∀ {n : ℕ} {Fin n ≃ A} (A : Type) → Type
Fac {n} {F≃A} A = Π x ∶ Fin n , {!  !}
  
 -- Π x ∶ (Fin n) , Fin (F→ℕ x)


-- Definition of Factorial
data Factorial : ℕ → Type where
  Φ! : {f : Fin 1} → Factorial 0
  ε! : {n : ℕ} → {f : Fin (suc n)} → Factorial n → Factorial (suc n)

-- Definition of C 
data Combin : ∀ {l m : ℕ} → Fin l → Fin m → Type where
  CΦ : Combin zero zero 
  Cε : {l m : ℕ} → {n k : Fin l} → Combin n k → Combin (suc n) k 
  Cχ : {l m : ℕ} → {n k : Fin l} → Combin n k → Combin (suc n) (suc k)

-- 

-- Σ-[x:_]_ : (List A) → (A → Type) → Type
-- Σ-[x: A ] F = F (x: A) ⊎ A


choose : {n : ℕ} → Type → ℕ → Type
choose {n} A zero = 𝟙
choose {n} A (suc k) = {! Σ A !}


```

-- calculus
open import Data.String using (String; _≟_)

Var : Type
Var = ℕ

-- infix  5  ƛ_⇒_
-- infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
-- infix  9  [_]
-- infix  9  ⟨_⟩

data Term : Type where
  `_                      : Var → Term
  _⨃_                     : Term → Term → Term
  _·_                     : Term → Term → Term
  Σ[_∈_]_                 : Var → Term → Term → Term
  Π[_∈_]_                 : Var → Term → Term → Term
  C[_,_]                  : Term → Var → Term 
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Var → Term → Term

  


data Value : Term → Type where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)


 


 



     
     
