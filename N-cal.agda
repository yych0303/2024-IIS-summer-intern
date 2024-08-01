open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.List.Base
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.String using (String; _≟_)


private Type = Set
private Type₁ = Set₁


-- Num


factorial : ℕ → ℕ 
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)

combination : ℕ → ℕ → ℕ
combination _ 0 = 1
combination 0 _ = 0
combination (suc i) (suc j) = combination i j + combination i (suc j) 

sigma[_]_ : List ℕ → (ℕ → ℕ) → ℕ
sigma[ [] ] F    = 0
sigma[ x ∷ l ] F = F x + sigma[ l ] F

pi[_]_ : List ℕ → (ℕ → ℕ) → ℕ
pi[ [] ] F    = 1
pi[ x ∷ l ] F = F x * sigma[ l ] F



-- N-calculus

Var St : Type
Var = String
Num = ℕ
St = List ℕ



infix  5 `Σ[_∈_]_ `Π[_∈_]_ 

infixl 6 `C[_,_]

infixl 7  _`*_
infixl 7  _`+_
infix  9  [_:=_]_
infix  9  `_ $_

data Term : Type₁ where
  `_                      : Num → Term
  $_                      : Var → Term
  _`+_                    : Term → Term → Term
  _`*_                    : Term → Term → Term
  `Σ[_∈_]_                : Var → St → Term → Term
  `Π[_∈_]_                : Var → St → Term → Term
  `C[_,_]                 : Term → Term → Term 

[_:=_]_ : Var → ℕ → Term → Term
[ v := n ] (` x)                    = ` x
[ v := n ] ($ x)        with x Data.String.≟ v
...                         | yes _ = ` n 
...                         | no  _ = $ x
[ v := n ] (t `+ t₁)                = [ v := n ] t `+ [ v := n ] t₁
[ v := n ] (t `* t₁)                = [ v := n ] t `* [ v := n ] t₁
[ v := n ] (`Σ[ x ∈ s ] t)          = `Σ[ x ∈ s ] [ v := n ] t
[ v := n ] (`Π[ x ∈ s ] t)          = `Π[ x ∈ s ] [ v := n ] t
[ v := n ] `C[ t , t₁ ]  = `C[ [ v := n ] t , [ v := n ] t₁ ]


{-# NON_TERMINATING #-}
eval : Term → ℕ

eval (` n)                       = n
eval ($ v)                      = 0 -- not possible
eval (t `+ t₁)                  = eval t + eval t₁
eval (t `* t₁)                  = eval t * eval t₁
eval (`Σ[ x ∈ s ] t₁)           = sigma[ s ] (λ n → eval ([ x := n ] t₁))
eval (`Π[ x ∈ s ] t₁)           = pi[ s ] (λ n → eval ([ x := n ] t₁))

eval `C[ t , t₁ ]                = combination (eval t) (eval t₁)

infix 1 eval


-- ev : ℕ
-- ev = eval (`Σ[ "x"  ∈  (12 ∷ 222 ∷ 32 ∷ []) ] $ "x"  ) 
 