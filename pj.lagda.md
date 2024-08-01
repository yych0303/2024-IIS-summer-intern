## Imports

```agda

------ std lib

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties

open import Data.Product using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

-- open import Data.Fin


open import Relation.Nullary using (¬_; Dec; yes; no)
-- open import Data.Unit using (⊤; tt)
-- open import Data.Empty using (⊥; ⊥-elim)

open import Level using (Level)

open import Function using (_∘_)
open import Function.Equivalence using (_⇔_)


------ plfa

open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning


------ file import
open import Logic

------------------------------------------------------------------------
```
## Goal

Goal:
(S ≃ T) ≃ (Fin n ≃ Fin m) ⇔ (N = M)

Example:
C n , k = Σ [n] (λ i → C (i-1) (k-1))




Num
1. type of combination
2. List 

Set
1. K A

Type
1. _×_ , _⊎_
2. Sg , Pi
3. _/_ , _-_
4. Fin
5. Factorial , Combination , Permutation







```agda

-- Num


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)

combination : ℕ → ℕ → ℕ
combination _ 0 = 1
combination 0 _ = 0
combination (suc i) (suc j) = combination i j + combination i (suc j) 

-- Sigma : 


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

Π : (A : Type) (B : A → Type) → Type
Π A B = (x : A) → B x

syntax Π A (λ x → b) = Π x ∈ A , b


-- Sg Type --------------------------------------

record Σ {a b} (A : Set) (B : A → Set) : Set  where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

syntax Σ A (λ x → b) = Σ x ∈ A , b


-- infixr 0 Σ_∈_,_ , Π_∈_,_


data _≣_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≣ x

infix 0 _≣_ 




-- Types ------------------------------------------------------------------------

-- Definition of Fin
data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)


𝟘 = Fin 0
𝟙 = Fin 1
𝟚 = Fin 2



{-- Example: 1 + 1 = 2
_ : Fin 1 ⊎ Fin 1 ≃ Fin 2
_ = record
  { to = λ { (inj₁ fzero) → (fzero {1}) ; (inj₂ fzero) → fsuc {1} fzero }
  ; from = λ { (fzero {1}) → inj₁ fzero ; (fsuc {1} fzero) → inj₂ fzero }
  ; from∘to = λ { (inj₁ x) → refl ; (inj₂ y) → refl }
  ; to∘from = λ { zero → refl ; suc zero → refl }
  }

-}

∥_∥ : Type → Type
∥ A ∥ = Σ n ∈ ℕ , (A ≃ Fin n)

-- Pow n k
-- Pow A B == A^B
Pow : Type → Type → Type
Pow A B = A → B

-- 

-- Definition of Identity mapping
-- id : (A : Type) → A → A 
-- id A a = a

Iso : Type → Type → Type
Iso A B = Σ f ∈ (A → B) , Σ g ∈ (B → A) , ( g ∘ f ≡ id {A} × f ∘ g ≡ id {B} ) 

Mono : Type → Type → Type
Mono A B = Σ f ∈ (A → B) , Π x ∈ A , Π y ∈ A , ((f x ≡ f y) → (x ≡ y))

-- Definition of Factorial 
-- Factorial : (A : Type) → Type
-- Type A 的所有排列

Factorial : Type → Type
Factorial A = A ≃ A



-- Definition of Factorial
-- data Factorial : ℕ → Type where
--   Φ! : {f : Fin 1} → Factorial 0
--   ε! : {n : ℕ} → {f : Fin (suc n)} → Factorial n → Factorial (suc n)


-- Definition of Permutation
-- Permutation : (A : Type) → (B : Type) → Type

Permutation : Type → Type → Type
Permutation A B = Mono B A
-- Permutation A B = Σ f ∈ (B → A) , Π x ∈ B , Π y ∈ B , ((f x ≡ f y) → (x ≡ y))


-- Definition of Div
-- Div : (A : Type) → (B : Type) → Type
Div : Type → Type → Type
Div A B = Σ n ∈ ℕ , (Fin n × (A ≃ B × Fin n))





-- 
-- Definition of Combination
-- Combination : (A : Type) → (B : Type) → Type

Combination : Type → Type → Type
Combination A B = {!   !}
  where 
    FA  = Factorial A
    PAB = Permutation A B



Combina : ℕ → ℕ → Type
Combina n k = {!   !}
 















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


 


 



     
     
