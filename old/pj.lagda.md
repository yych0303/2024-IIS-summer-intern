## Imports

```agda

------ std lib
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

-- open import Data.Bool -- using (Bool; true; false; T; _∧_; _∨_; not)
-- open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties

open import Data.Product -- using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ) renaming (suc to fsuc ; zero to fzero)


open import Data.List.Base


-- open import Relation.Nullary using (¬_; Dec; yes; no)

open import Level using (Level)

open import Function using (_∘_)
-- open import Function.Equivalence using (_⇔_)
open import Function.Dependent.Bundles


------ plfa
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning


------ file import
open import Logic
open import N-cal

------ private
private Type = Set
private Type₁ = Set₁

------------------------------------------------------------------------
```
## Goal

Goal:
(S ≃ T) ≃ (Fin n ≃ Fin m) ⇔ (N = M)

Example:
C n , k = Σ i ∈ [n] , (C (i-1) (k-1))





Computation Num
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

N-calculus





```agda


{-
-- https://agda.github.io/agda-stdlib/master/Data.Product.Base.html
------------------------------------------------------------------------
-- Existential quantifiers

∃ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

------------------------------------------------------------------------
-- Syntaxes

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infix 2 ∃-syntax

∃-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

-}

-- Pi Type --------------------------------------




Π-syntax : (A : Type) (B : A → Type) → Type
Π-syntax A B = (x : A) → B x

syntax  Π-syntax A (λ x → b) = Π[ x ∈ A ] b
infix 2 Π-syntax


data _≣_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≣ x

infix 0 _≣_ 


-- Types ------------------------------------------------------------------------


∥_∥ : Type → Type
∥ A ∥ = (A → ⊥) → ⊥

-- Pow n k
-- Pow A B == A^B
Pow : Type → Type → Type
Pow A B = A → B




Bijection : Type → Type → Type
Bijection A B = Σ[ f ∈ (A → B) ] Σ[ g ∈ (B → A) ] ( g ∘ f ≡ id {A} × f ∘ g ≡ id {B} ) 


Injection : Type → Type → Type
Injection A B = Σ[ f ∈ (A → B) ] Π[ x ∈ A ] Π[ y ∈ A ] ((f x ≡ f y) → (x ≡ y))




-- Definition of Factorial 
-- Factorial : (A : Type) → Type
-- Type A 的所有排列

Factorial : Type → Type
Factorial A = Bijection A A
-- Factorial A = A ≃ A




-- Definition of Permutation
-- Permutation : (A : Type) → (B : Type) → Type

Permutation : Type → Type → Type
Permutation A B = Injection B A
-- Permutation A B = Σ f ∈ (B → A) , Π x ∈ B , Π y ∈ B , ((f x ≡ f y) → (x ≡ y))


-- Definition of Div
-- Div : (A : Type) → (B : Type) → Type
Div : Type → Type → Type
Div A B = Σ[ n ∈ ℕ ] (Fin n × (A ≃ B × Fin n))





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



-- F-Types

eqFin : Type → Type
eqFin A = Σ[ n ∈ ℕ ] (A ≃ Fin n)

e : eqFin (Fin 3) 
e = 3 , {!   !}

-- Fin post
postulate
  -- F⊥ : Fin 0 ≃ ⊥
  -- F⊤ : Fin 1 ≃ ⊤

  F0⊎Fn : ∀ {n : ℕ} → ((Fin 0 ⊎ Fin n) ≃ Fin n)
  Fn⊎F0 : ∀ {n : ℕ} → ((Fin n ⊎ Fin 0) ≃ Fin n)
  Fm⊎Fn : ∀ {m n : ℕ} → ((Fin m ⊎ Fin n) ≃ Fin (m + n))

  F1×Fn : ∀ {n : ℕ} → ((Fin 1 × Fin n) ≃ Fin n)
  Fn×F1 : ∀ {n : ℕ} → ((Fin n × Fin 1) ≃ Fin n)
  Fm×Fn : ∀ {m n : ℕ} → ((Fin m × Fin n) ≃ Fin (m * n))

  F→ℕ : ∀ {m n : ℕ} → ((Fin m ≃ Fin n) → (m ≡ n))
  

Q : Fin 3 ⊎ Fin 4 ≃ Fin 7
Q = 
  ≃-begin 
    (Fin 3 ⊎ Fin 4)  
  ≃⟨ Fm⊎Fn {3} {4} ⟩
    Fin 7
  ≃-∎



neqFin : {n : ℕ} → Type → Type
neqFin {n} A = (A ≃ Fin n)

ne : neqFin {3} (Fin 3) 
ne = {!   !}



F-Factorial : ℕ → Type
F-Factorial 0 = Fin 1
F-Factorial (suc n) = Fin (suc n) × F-Factorial n




{-

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

-}




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
  


-- Definition of Factorial
-- data Factorial : ℕ → Type where
--   Φ! : {f : Fin 1} → Factorial 0
--   ε! : {n : ℕ} → {f : Fin (suc n)} → Factorial n → Factorial (suc n)



-- create Comb 

⟦_⟧ : ℕ → Comb
⟦ zero ⟧ = Φ
⟦ suc n ⟧ = ε {suc n} ⟦ n ⟧

-}

ringType : Ring Type
ringType = record
  { R0   = Fin 0
  ; R1   = Fin 1
  ; _R+_ = _⊎_
  ; _R*_ = _×_
  ; RIdx   = λ x → Fin 0
  ; RP   = {!   !}
  ; RC   = {!   !}
  }


funcℕType = Fin

evalType = eval ringType


-- et = evalType (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] ($ "x") ) 


```


infix 4 _≈_

data _≈_ : Type → Type → Set where

  0-∙₂
  

  0-∙₁ : ∀ {L}
    → L ∙ Fin 0 ≈ L

  0-∙₂
  
  ξ-∙₁ : ∀ {L L′ M}
    → L ≈ L′
      -----------------
    → L ∙ M ≈ L′ ∙ M

  ξ-∙₂ : ∀ {V M M′}
    → Value V
    → M ≈ M′
      -----------------
    → V ∙ M ≈ V ∙ M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) ∙ V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

        



  
 

 



       
           