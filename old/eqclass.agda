-- file import
open import Logic
open import N-cal

-- std lib

open import Relation.Binary.Core 

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

-- open Eq.≡-Reasoning

-- open import Data.Bool -- using (Bool; true; false; T; _∧_; _∨_; not)
-- open import Data.Unit  using (⊤; tt)
-- open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
-- open import Data.Nat.Properties

-- open import Data.Product -- using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

-- open import Data.Fin using (Fin; toℕ; Fin′; cast; fromℕ) renaming (suc to fsuc ; zero to fzero)


-- open import Data.List.Base


-- open import Relation.Nullary using (¬_; Dec; yes; no)

-- open import Level using (Level)

-- open import Function using (_∘_)
-- open import Function.Equivalence using (_⇔_)
-- open import Function.Dependent.Bundles


------ plfa
-- open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_; ≃-trans)



private
  variable
    ℓ ℓ₁ : Level
    A : Set
---------------------------------------------------------------------

{-

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ



-- Rel A
_≃_ : A → A → Set  

-- Rel in Term A

_≈[_]_ : {A : Set} → Rel A → Rel (Term A)
a ≈[≃] b  =  evalA a ≃ evalA b




a ≈ b iff evalA a ≃ evalA b


record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

_≃_ : {A : Set ℓ} → Rel A ℓ
a ≃ b = {!   !}



<_,_>_≈_ : {A : Set ℓ} → Ring A → Rel A ℓ → Rel (Term A) ℓ
< ringA , _rl_ > ta ≈ tb = (eval ringA ta) rl (eval ringA tb)


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
-}


record E (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _∼_ : A → A → Set 


eℕ : E ℕ
eℕ = record { _∼_  = _≡_ }

eList : E (List ℕ)
eList = record { _∼_  = {!   !} }


est : E (St A)
est = record { _∼_  = {!   !} }


{-


  Term A -- trns funcAℕ -> Term ℕ
    |                        |
    |                        |
eval ringA               eval ringℕ
    |                        |
    V                        V
    A ------- funcAℕ ------> ℕ

 ta ≈ ta' <----- ? -----> tn ≈ tn'
    Λ                        Λ
    |                        |
   def                      def
    |                        |
    |                        |
  a ∼ a' - _=[funcAℕ]_⇒ ->  n ≡ n'




-}

open import Relation.Binary.Core
open import Relation.Binary.Bundles
variable 
  c : Level

infix 0 _≈_
record _≈_ {A :  Setoid c ℓ} {ring : Ring A} {_~_  : A → A → Set} (ta tb : Term A) : Set (lsuc ℓ) where
  field
    equiv : eval ring ta ~ eval ring tb
open _≈_

≈-refl : ∀ {A : Set} {ta : Term A}
    -----
  → ta ≈ ta
≈-refl = {!  !}

≈-sym : ∀ {A : Set} {ta tb : Term A}
  → ta ≈ tb
    -----
  → tb ≈ ta
≈-sym A≈B = {!   !}

≈-trans : ∀ {A : Set} {ta tb tc : Term A}
  → ta ≈ tb
  → tb ≈ tc
    -----
  → ta ≈ tc
≈-trans ta≈tb tb≈ta = {!   !}

module ≈-Reasoning where

  infix  1 ≈-begin_
  infixr 2 _≈⟨_⟩_
  infix  3 _≈-∎

  ≈-begin_ : ∀ {A : Set} {ta tb tc : Term A}
    → ta ≈ tb
      -----
    → ta ≈ tb
  ≈-begin ta≈tb = ta≈tb

  _≈⟨_⟩_ : ∀ {A : Set} → (ta : Term A) {tb tc : Term A}
    → ta ≈ tb
    → tb ≈ tc
      -----
    → ta ≈ tc
  ta ≈⟨ ta≈tb ⟩ tb≈tc = ≈-trans ta≈tb tb≈tc

  _≈-∎ : ∀ {A : Set} → (ta : Term A)
      -----
    → ta ≈ ta
  ta ≈-∎ = ≈-refl

open ≈-Reasoning



















{-

infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infix  3 _≃-∎

≃-begin_ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≃ B
≃-begin A≃B = A≃B

_≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

_≃-∎ : ∀ (A : Set)
    -----
  → A ≃ A
A ≃-∎ =  ≃-refl


-}