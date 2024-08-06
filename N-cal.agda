module N-cal where
open import Agda.Primitive
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.List.Base public
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.String using (String; _≟_) public

private
  variable
    ℓ ℓ₁ : Level
-- N-calculus
{-
main frame
...

  Term A -- trns funcAB -> Term B
    |                        |
    |                        |
eval ringA               eval ringB
    |                        |
    V                        V
    A ------- funcAB ------> B



data Term (Val : Set ℓ) : Set ℓ
  `_ | $_ | _`+_ | _`*_ | `Σ[_∈_]_ | `Π[_∈_]_ | 
  [_]`! | `P[_,_] | `C[_,_] 





record Ring (R : Type) : Type


[_:=_]_ : {ℓ : Level} {Val : Set ℓ} → Idx → Val → Term Val → Term Val


eval : {ℓ : Level} {R : Set ℓ} → (Ring {ℓ} R) → Term R → R



ring 
...
ringℕ
ringSt
ringListℕ


 
trns : {R R' : Set} → (R → R') → Term R → Term R'


func
...
funcℕStℕ
funcℕListℕ





-}

-- Term --------------------------------------------------------------

infix  5 `Σ[_∈_]_ `Π[_∈_]_ 
infixl 6 `C[_,_]  `P[_,_]
infixl 7  _`*_
infixl 7  _`+_
infix  9  [_:=_]_
infixl 9  [_]`!
infix  9  `_ $_

private Idx : Set
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


-- Ring (Set) : Set -------------------------------------------------------

record Ring {ℓ : Level} (R : Set ℓ) : Set (lsuc ℓ) where
  field
    R0          : R
    R1          : R
    _R+_        : R → R → R
    _R*_        : R → R → R
    RIdx        : Idx → R
    RP          : R → R → R
    RC          : R → R → R
open Ring


-- [:=] ---------------------------------------------------------------------

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



-- eval : EvalOps → Term Val → R ----------------------

private rsigma : {ℓ : Level} {R : Set ℓ} → (Ring {ℓ} R) → List R → (R → R) → R
rsigma ring []      F = R0   ring
rsigma ring (i ∷ l) F = _R+_ ring (F i) (rsigma ring l F)

private rpi : {ℓ : Level} {R : Set ℓ} → (Ring {ℓ} R) → List R → (R → R) → R
rpi ring []      F = R1   ring
rpi ring (i ∷ l) F = _R*_ ring (F i) (rsigma ring l F)

private r! : {ℓ : Level} {R : Set ℓ} → (Ring {ℓ} R) → R → R
r! ring r =  RP ring r r 

-- RC : {ℓ ℓ₁ : Level} (ring : EvalOps {ℓ} {ℓ₁}) → R ring → Val ring → R ring
-- RC ring a k = {!  !}

-- private RP : {ℓ ℓ₁ : Level} (ring : EvalOps {ℓ} {ℓ₁}) → R ring → R ring → R ring
-- RP ring R B = R! ring {!   !}


infix 1 eval

{-# NON_TERMINATING #-}
eval : {ℓ : Level} {R : Set ℓ} → (Ring {ℓ} R) → Term R → R
eval ring term with term
...     | (` v)            = v
...     | ($ i)            = RIdx    ring i -- not possible
...     | (t `+ t₁)        = _R+_    ring (eval ring t) (eval ring t₁)
...     | (t `* t₁)        = _R*_    ring (eval ring t) (eval ring t₁)
...     | `P[ t , t₁ ]     = RP      ring (eval ring t) (eval ring t₁)
...     | `C[ t , t₁ ]     = RC      ring (eval ring t) (eval ring t₁)
...     | (`Σ[ i ∈ l ] t)  = rsigma  ring l (λ v → eval ring ([ i := v ] t))
...     | (`Π[ i ∈ l ] t)  = rpi     ring l (λ v → eval ring ([ i := v ] t))
...     | [ t ]`!          = r!      ring (eval ring t)


-- Ring ℕ ---------------------------------------------------------------------

ringℕ : Ring ℕ
ringℕ = record
  { R0   = 0
  ; R1   = 1
  ; _R+_ = _+_
  ; _R*_ = _*_
  ; RIdx   = λ x → 0
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



evalℕ : Term ℕ → ℕ
evalℕ = eval ringℕ


private ev : ℕ  -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
ev = evalℕ (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ]  ) 



private er = λ n → λ k → evalℕ `C[ ` n `+ ` k , ` k ] 
-- _ = λ n → λ k → `C[ ` n `+ ` k , ` n ]
-- = λ n k → N-cal.combination (n + k) k



-- Ring (St A) ---------------------------------------------------- 

St : Set → Set
St A = List (List A)


ringSt : {A : Set} → Ring (St A)
ringSt = record
  { R0   = []
  ; R1   = [ [] ]
  ; _R+_ = _++_
  ; _R*_ = prod
  ; RIdx   = λ x → []
  ; RP   = λ xs ys → permutation xs (length ys)
  ; RC   = λ xs ys → combination xs (length ys)
  }
    where
      prod : {A : Set} → St A → St A → St A
      prod = λ xs ys → concatMap (λ x → map (x ++_) ys ) xs
      
      permutation : {A : Set} → St A → ℕ → St A
      permutation _  0  = [ [] ]
      permutation [] _  = []
      permutation (l ∷ ls) (suc k) = prod (l ∷ ls)  (permutation ls k)

      combination : {A : Set} → St A → ℕ → St A
      combination _  0 = [ [] ]
      combination [] _ = []
      combination (l ∷ ls) (suc k) = map (l ++_) (combination ls k) ++ combination ls (suc k)
  

evalSt : {A : Set} → Term (St A) → St A
evalSt {A} = eval (ringSt {A})

-- Ring (List ℕ) -----------------------------------------------


ringListℕ : Ring (List ℕ)
ringListℕ = record  
  { R0   = r0
  ; R1   = r1
  ; _R+_ = _++_
  ; _R*_ = λ xs ys → concatMap (λ x → map (x *_) ys) xs
  ; RIdx   = λ x → []
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

evalListℕ : Term (List ℕ) → List ℕ
evalListℕ = eval ringListℕ



-- trns -----------------------------------------------------------------

infix 1 trns

{-# NON_TERMINATING #-}
trns : {R R' : Set} → (R → R') → Term R → Term R'
trns func term with term
...     | (` v)            = (` (func v))          
...     | ($ i)            = ($ i)          
...     | (t `+ t₁)        = (trns func t `+ trns func t₁)      
...     | (t `* t₁)        = (trns func t `* trns func t₁)      
...     | `P[ t , t₁ ]     = `P[ trns func t , trns func t₁ ]   
...     | `C[ t , t₁ ]     = `C[ trns func t , trns func t₁ ]   
...     | (`Σ[ i ∈ l ] t)  = (`Σ[ i ∈ map func l ] trns func t)
...     | (`Π[ i ∈ l ] t)  = (`Π[ i ∈ map func l ] trns func t)
...     | [ t ]`!          = [ trns func t ]`!        


-- func ------------------------------------------------------------------

funcℕStℕ : ℕ → St ℕ
funcℕStℕ = λ n → map [_] (iterate suc 0 n)

funcℕListℕ : ℕ → List ℕ
funcℕListℕ = [_]ᶜ
    where
      [_]ᶜ : ℕ → List ℕ
      [ n ]ᶜ = iterate suc 0 n













{-

OrdRing : (R : Set ℓ₁) 
        → (R0 : R) 
        → (RS : R → R) 
        → (R+ : R → R → R)
        → (R* : R → R → R)
        ------------------
        → Ring R
OrdRing r r0 rs r+ r* = record
  { R0   = r0
  ; R1   = r1
  ; _R+_ = r+
  ; _R*_ = r*
  ; RP   = rP
  ; RC   = rC
  }
    where
      r1 = rs r0
        
      rP : R → R → R
      rP _  0 = r1
      rP [] _ = r0
      rP (x ∷ xs) (suc k) = r* (x ∷ xs) (rP xs k)
      
      rC : R → R → R
      rC _ 0 = r1
      rC [] _ = r0
      rC (rs rn) (rs rk) = rC xs (suc j) ++ rC xs j



-}









      -- factorial : ℕ → ℕ 
      -- factorial zero = 1
      -- factorial (suc n) = (suc n) * (factorial n)




   