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
    a b ℓ : Level
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

-- Val  A   --  ops
------------
-- ℕ    ℕ      opsℕ
-- ℕ   Type   opsType
-- 

data Term (Val : Set a) : Set a where
  `_         : Val → Term Val
  $_         : Idx → Term Val
  _`+_       : Term Val → Term Val → Term Val
  _`*_       : Term Val → Term Val → Term Val
  `Σ[_∈_]_   : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_   : Idx → List Val → Term Val → Term Val
  `C[_,_]    : Term Val → Term Val → Term Val
--  _`!      : Term Val → Term Val



[_:=_]_ : {a : Level} {Val : Set a} → Idx → Val → Term Val → Term Val
[ v := n ] (` x)                    = ` x
[ v := n ] ($ x) with x Data.String.≟ v
...                         | yes _ = ` n 
...                         | no  _ = $ x
[ v := n ] (t `+ t₁)                = [ v := n ] t `+ [ v := n ] t₁
[ v := n ] (t `* t₁)                = [ v := n ] t `* [ v := n ] t₁
[ v := n ] (`Σ[ x ∈ s ] t)          = `Σ[ x ∈ s ] [ v := n ] t
[ v := n ] (`Π[ x ∈ s ] t)          = `Π[ x ∈ s ] [ v := n ] t
[ v := n ] `C[ t , t₁ ]             = `C[ [ v := n ] t , [ v := n ] t₁ ]


record EvalOps  : Set (lsuc (a ⊔ b)) where
  field
    Val         : Set a
    A           : Set b
    Ae          : Val → A
    Av          : Idx → A
    A0          : A
    A1          : A
    _A+_        : A → A → A
    _A*_        : A → A → A
    AC          : A → A → A

_Asigma[_]_ : {a b : Level} (ops : EvalOps {a} {b}) → List (EvalOps.Val ops) → (EvalOps.Val ops → EvalOps.A ops) → EvalOps.A ops
ops Asigma[ [] ] F    = EvalOps.A0 ops
ops Asigma[ e ∷ l ] F = EvalOps._A+_ ops (F e) (ops Asigma[ l ] F)

_Api[_]_ : {a b : Level} (ops : EvalOps {a} {b}) → List (EvalOps.Val ops) → (EvalOps.Val ops → EvalOps.A ops) → EvalOps.A ops
ops Api[ [] ] F    = EvalOps.A1 ops
ops Api[ e ∷ l ] F = EvalOps._A*_ ops (F e) (ops Asigma[ l ] F)

-- AC : {a b : Level} (ops : EvalOps {a} {b}) → EvalOps.A ops → EvalOps.Val ops → EvalOps.A ops
-- AC ops a k = {!  !}

-- _A!_ : {a b : Level} (ops : EvalOps {a} {b}) → EvalOps.Val ops → EvalOps.A ops
-- ops A! e =  ops Api[ ] 


{-# NON_TERMINATING #-}
eval : {a b : Level} (ops : EvalOps {a} {b}) → Term (EvalOps.Val ops) → (EvalOps.A ops)

eval ops (` e)            = EvalOps.Ae ops            e
eval ops ($ v)            = EvalOps.Av ops            v -- not possible
eval ops (t `+ t₁)        = EvalOps._A+_ ops          (eval ops t) (eval ops t₁)
eval ops (t `* t₁)        = EvalOps._A*_ ops          (eval ops t) (eval ops t₁)
eval ops (`Σ[ v ∈ s ] t)  = ops Asigma[ s ]   (λ n → eval ops ([ v := n ] t))
eval ops (`Π[ v ∈ s ] t)  = ops Api[ s ]      (λ n → eval ops ([ v := n ] t))
eval ops `C[ t , t₁ ]     = EvalOps.AC ops            (eval ops t) (eval ops t₁)

infix 1 eval


-- ℕ ---------------------------------------------------------------------


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)

combination : ℕ → ℕ → ℕ
combination _ 0 = 1
combination 0 _ = 0
combination (suc i) (suc j) = combination i j + combination i (suc j) 

{-

sigma[_]_ : List ℕ → (ℕ → ℕ) → ℕ
sigma[ [] ] F    = 0
sigma[ x ∷ l ] F = F x + sigma[ l ] F

pi[_]_ : List ℕ → (ℕ → ℕ) → ℕ
pi[ [] ] F    = 1
pi[ x ∷ l ] F = F x * sigma[ l ] F

-}


opsℕ = record 
  { Val  = ℕ
  ; A    = ℕ
  ; Ae   = λ x → x
  ; Av   = λ x → 0 -- __
  ; A0   = 0
  ; A1   = 1
  ; _A+_ = _+_
  ; _A*_ = _*_
  ; AC   = combination
  }

evalℕ : Term ℕ → ℕ
evalℕ = eval opsℕ


ev : ℕ  -- sigma x ∈ {2, 3, 4} Cx , 2
ev = evalℕ (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ]  ) 



er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 
-- _ = λ n → λ k → `C[ ` n `+ ` k , ` n ]





        