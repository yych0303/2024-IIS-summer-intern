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


infix  5 `Σ[_∈_]_ `Π[_∈_]_ 
infixl 6 `C[_,_]  `P[_,_]
infixl 7  _`*_
infixl 7  _`+_
infix  9  [_:=_]_
infixl 9  [_]`!
infix  9  `_ $_

private Idx : Type
Idx = String

data Term (Val : Set ℓ) : Set ℓ where
  `_          : Val → Term Val
  $_          : Idx → Term Val
  _`+_        : Term Val → Term Val → Term Val
  _`*_        : Term Val → Term Val → Term Val
  `Σ[_∈_]_    : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_    : Idx → List Val → Term Val → Term Val
  [_]`!       : Term Val → Term Val
  `P[_,_]     : Term Val → Term Val → Term Val
  `C[_,_]     : Term Val → Term Val → Term Val



[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val
[ i := v ] (` x)                    = ` x
[ i := v ] ($ x) with x Data.String.≟ i
...                         | yes _ = ` v 
...                         | no  _ = $ x
[ i := v ] (t `+ t₁)                = [ i := v ] t `+ [ i := v ] t₁
[ i := v ] (t `* t₁)                = [ i := v ] t `* [ i := v ] t₁
[ i := v ] (`Σ[ x ∈ s ] t)          = `Σ[ x ∈ s ] [ i := v ] t
[ i := v ] (`Π[ x ∈ s ] t)          = `Π[ x ∈ s ] [ i := v ] t
[ i := v ] [ t ]`!                  = [ [ i := v ] t ]`!
[ i := v ] `P[ t , t₁ ]             = `P[ [ i := v ] t , [ i := v ] t₁ ]
[ i := v ] `C[ t , t₁ ]             = `C[ [ i := v ] t , [ i := v ] t₁ ]



-- EvalOps  : Set ----------------------------------

record Ring (R : Set ℓ₁) : Set ℓ₁ where
  field
    R0          : R
    R1          : R
    _R+_        : R → R → R
    _R*_        : R → R → R
    RP          : R → R → R
    RC          : R → R → R
open Ring

record EvalOps  : Set (lsuc (ℓ ⊔ ℓ₁)) where
  field
    Val         : Set ℓ
    R           : Set ℓ₁
    rVal        : Val → R
    rIdx        : Idx → R
    ring        : Ring R
open EvalOps
    





-- eval : EvalOps → Term Val → R ----------------------

private rsigma : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → List (Val ops) → (Val ops → R ops) → R ops
rsigma ops []      F = R0   (ring ops)
rsigma ops (i ∷ l) F = _R+_ (ring ops) (F i) (rsigma ops l F)

private rpi : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → List (Val ops) → (Val ops → R ops) → R ops
rpi ops []      F = R1   (ring ops)
rpi ops (i ∷ l) F = _R*_ (ring ops) (F i) (rsigma ops l F)

private r! : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → R ops → R ops
r! ops r =  RP (ring ops) r r 

-- RC : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → R ops → Val ops → R ops
-- RC ops a k = {!  !}

-- private RP : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → R ops → R ops → R ops
-- RP ops A B = R! ops {!   !}


infix 1 eval

{-# NON_TERMINATING #-}
eval : {ℓ ℓ₁ : Level} (ops : EvalOps {ℓ} {ℓ₁}) → Term (Val ops) → R ops

eval ops term with term
...    | (` v)            = rVal    ops v
...    | ($ i)            = rIdx    ops i -- not possible
...    | (t `+ t₁)        = _R+_    (ring ops) (eval ops t) (eval ops t₁)
...    | (t `* t₁)        = _R*_    (ring ops) (eval ops t) (eval ops t₁)
...    | `P[ t , t₁ ]     = RP      (ring ops) (eval ops t) (eval ops t₁)
...    | `C[ t , t₁ ]     = RC      (ring ops) (eval ops t) (eval ops t₁)
...    | (`Σ[ i ∈ l ] t)  = rsigma  ops l (λ v → eval ops ([ i := v ] t))
...    | (`Π[ i ∈ l ] t)  = rpi     ops l (λ v → eval ops ([ i := v ] t))
...    | [ t ]`!          = r!      ops (eval ops t)


-- ℕ ---------------------------------------------------------------------

ringℕ : Ring ℕ
ringℕ = record
  { R0   = 0
  ; R1   = 1
  ; _R+_ = _+_
  ; _R*_ = _*_
  ; RP   = permutation
  ; RC   = combination
  }
    where      
      permutation : ℕ → ℕ → ℕ
      permutation _ 0 = 1
      permutation 0 _ = 0
      permutation (suc i) (suc j) = (suc i) * permutation i j 

      combination : ℕ → ℕ → ℕ
      combination _ 0 = 1
      combination 0 _ = 0
      combination (suc i) (suc j) = combination i j + combination i (suc j) 


opsℕ = record 
  { Val  = ℕ
  ; R    = ℕ
  ; rVal   = λ x → x
  ; rIdx   = λ x → 0 -- __
  ; ring = ringℕ
  }   

evalℕ : Term ℕ → ℕ
evalℕ = eval opsℕ


private ev : ℕ  -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
ev = evalℕ (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ]  ) 



private er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 
-- _ = λ n → λ k → `C[ ` n `+ ` k , ` n ]
-- = λ n k → N-cal.combination (n + k) k



-- Ring (List (List A)) ---------------------------------------------------- 

ringSt : {A : Type} → Ring (List (List A))
ringSt = record
  { R0   = []
  ; R1   = [ [] ]
  ; _R+_ = _++_
  ; _R*_ = prod
  ; RP   = λ xs ys → permutation xs (length ys)
  ; RC   = λ xs ys → combination xs (length ys)
  }
    where
      prod : {A : Type} → List (List A) → List (List A) → List (List A)
      prod = λ xs ys → concatMap (λ x → map (x ++_) ys ) xs
      
      permutation : ∀ {A : Type} → List (List A) → ℕ → List (List A)
      permutation _  0  = [ [] ]
      permutation [] _  = []
      permutation (l ∷ ls) (suc k) = prod (l ∷ ls)  (permutation ls k)

      combination : {A : Type} → List (List A) → ℕ → List (List A)
      combination _  0 = [ [] ]
      combination [] _ = []
      combination (l ∷ ls) (suc k) = map (l ++_) (combination ls k) ++ combination ls (suc k)
  

opsSt = record 
  { Val  = ℕ
  ; R    = List (List ℕ)
  ; rVal   = λ n → map [_] (iterate suc 0 n)
  ; rIdx   = λ x → []
  ; ring = ringSt
  }

evalSt = eval opsSt

-- Ring (List ℕ) -----------------------------------------------


ringListℕ : Ring (List ℕ)
ringListℕ = record  
  { R0   = r0
  ; R1   = r1
  ; _R+_ = _++_
  ; _R*_ = λ xs ys → concatMap (λ x → map (x *_) ys) xs
  ; RP   = λ x y → rP x (length y)
  ; RC   = λ x y → rC x (length y)
  }
    where
      r0 = []
      r1 = [ 1 ]
      r* = λ xs ys → concatMap (λ x → map (x *_) ys) xs
      
      rP : List ℕ → ℕ → List ℕ
      rP _  0 = r1
      rP [] _ = r0
      rP (x ∷ xs) (suc k) = r* (x ∷ xs) (rP xs k)
      
      rC : List ℕ → ℕ → List ℕ
      rC _ 0 = r1
      rC [] _ = r0
      rC (x ∷ xs) (suc j) = rC xs (suc j) ++ rC xs j

opsListℕ = record 
  { Val  = ℕ
  ; R    = List ℕ
  ; rVal   = [_]ᶜ
  ; rIdx   = λ x → []
  ; ring = ringListℕ
  }
    where
      [_]ᶜ : ℕ → List ℕ
      [ n ]ᶜ = iterate suc 0 n
    
evalListℕ = eval opsListℕ








      -- factorial : ℕ → ℕ 
      -- factorial zero = 1
      -- factorial (suc n) = (suc n) * (factorial n)




