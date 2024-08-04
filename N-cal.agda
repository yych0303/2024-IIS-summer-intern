module N-cal where
open import Agda.Primitive
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.List.Base public
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.String using (String; _≟_) public

private Type = Set
private Type₁ = Set₁

private
  variable
    ℓ ℓ₁ : Level
-- N-calculus

Idx : Type
Idx = String

infix  5 `Σ[_∈_]_ `Π[_∈_]_ 
infixl 6 `C[_,_]
infixl 7  _`*_
infixl 7  _`+_
infix  9  [_:=_]_
infix  9  `_ $_

-- idx = String 

-- Val  R   --  ops
------------
-- ℕ    ℕ      opsℕ
-- ℕ   Type   opsType
-- 

data Term (Val : Set ℓ) : Set ℓ where
  `_         : Val → Term Val
  $_         : Idx → Term Val
  _`+_       : Term Val → Term Val → Term Val
  _`*_       : Term Val → Term Val → Term Val
  `Σ[_∈_]_   : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_   : Idx → List Val → Term Val → Term Val
  `C[_,_]    : Term Val → Term Val → Term Val
-- `P[_,_]    : Term Val → Term Val → Term Val
--  _`!      : Term Val → Term Val



[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val
[ v := n ] (` x)                    = ` x
[ v := n ] ($ x) with x Data.String.≟ v
...                         | yes _ = ` n 
...                         | no  _ = $ x
[ v := n ] (t `+ t₁)                = [ v := n ] t `+ [ v := n ] t₁
[ v := n ] (t `* t₁)                = [ v := n ] t `* [ v := n ] t₁
[ v := n ] (`Σ[ x ∈ s ] t)          = `Σ[ x ∈ s ] [ v := n ] t
[ v := n ] (`Π[ x ∈ s ] t)          = `Π[ x ∈ s ] [ v := n ] t
[ v := n ] `C[ t , t₁ ]             = `C[ [ v := n ] t , [ v := n ] t₁ ]


record EvalOps  : Set (lsuc (ℓ ⊔ ℓ₁)) where
  field
    Val         : Set ℓ
    R           : Set ℓ₁
    Rv          : Val → R
    Ri          : Idx → R
    R0          : R
    R1          : R
    _R+_        : R → R → R
    _R*_        : R → R → R
    RC          : R → R → R

_Rsigma[_]_ : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → List (EvalOps.Val ops) → (EvalOps.Val ops → EvalOps.R ops) → EvalOps.R ops
ops Rsigma[ [] ] F    = EvalOps.R0 ops
ops Rsigma[ e ∷ l ] F = EvalOps._R+_ ops (F e) (ops Rsigma[ l ] F)

_Rpi[_]_ : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → List (EvalOps.Val ops) → (EvalOps.Val ops → EvalOps.R ops) → EvalOps.R ops
ops Rpi[ [] ] F    = EvalOps.R1 ops
ops Rpi[ e ∷ l ] F = EvalOps._R*_ ops (F e) (ops Rsigma[ l ] F)

-- RC : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → EvalOps.R ops → EvalOps.Val ops → EvalOps.R ops
-- RC ops a k = {!  !}

-- _R!_ : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → EvalOps.Val ops → EvalOps.R ops
-- ops R! e =  ops Rpi[ ] 


{-# NON_TERMINATING #-}
eval : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → Term (EvalOps.Val ops) → (EvalOps.R ops)

eval ops (` e)            = EvalOps.Rv ops            e
eval ops ($ v)            = EvalOps.Ri ops            v -- not possible
eval ops (t `+ t₁)        = EvalOps._R+_ ops          (eval ops t) (eval ops t₁)
eval ops (t `* t₁)        = EvalOps._R*_ ops          (eval ops t) (eval ops t₁)
eval ops (`Σ[ v ∈ s ] t)  = ops Rsigma[ s ]   (λ n → eval ops ([ v := n ] t))
eval ops (`Π[ v ∈ s ] t)  = ops Rpi[ s ]      (λ n → eval ops ([ v := n ] t))
eval ops `C[ t , t₁ ]     = EvalOps.RC ops            (eval ops t) (eval ops t₁)

infix 1 eval


-- ℕ ---------------------------------------------------------------------


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)

combination : ℕ → ℕ → ℕ
combination _ 0 = 1
combination 0 _ = 0
combination (suc i) (suc j) = combination i j + combination i (suc j) 


opsℕ = record 
  { Val  = ℕ
  ; R    = ℕ
  ; Rv   = λ x → x
  ; Ri   = λ x → 0 -- __
  ; R0   = 0
  ; R1   = 1
  ; _R+_ = _+_
  ; _R*_ = _*_
  ; RC   = combination
  }

evalℕ : Term ℕ → ℕ
evalℕ = eval opsℕ


ev : ℕ  -- sigma x ∈ {2, 3, 4} Cx , 2
ev = evalℕ (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ]  ) 



er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 
-- _ = λ n → λ k → `C[ ` n `+ ` k , ` n ]

