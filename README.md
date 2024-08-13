# Bridging Combinatorial and Algebraic proof: An Algebraic Approach with Agda

## Abstract

在證明組合恆等式時，有多種不同的方式可以闡述證明，其中包括代數論證和組合論證。組合論證主要依賴於雙重計數（Double counting）和對應論證（bijective proof）兩種技術，前者透過兩種方式構造同一集合來證明恆等式，後者則透過建立兩個集合之間的一一對應來論證。代數論證則依賴於代數運算的特性或定理來證明恆等式。

本文探討如何使用Agda來驗證代數論證與組合論證之間的等價性，通過抽象出兩者的共同代數結構，並證明在Agda中保持這些證明正確性所需的條件，進而建立兩種論證方式之間的等價性 S ≃ S' ↔ n = n'，

#### kws: 
Agda; Commutative ring; Finset; Combinatorial reasoning; Double counting

## Motivation
在學習過程中，組合論證因其直觀的組合意義而更容易理解和構建，而代數證明往往需要通過大量輔助引理的堆砌。為了驗證這兩種證明方法的等價性，本研究希望通過Agda抽象出兩者的共同代數結構，從而系統化地構建組合證明的正確性並探討其等價關係。




ex. ![image](https://hackmd.io/_uploads/ryuXteQq0.png)





### Main frame

```n
[Interface]             Term A <-------- trns ---------> Term B   
    |                     |               ~                |      
    | implements          |              func              |      
    V                     |                                |      
[abstract]                |     Ring   Embedding           |      
    |                     |       |        |               |      
    | inherits            |       ∈        ~               |      
    V                     |       |        |               |      
[concrete]              eval <~ ringA <- conv -> ringB ~> eval    
    |                     |    /                      \    |      
    | instantiates        |   /                        \   |      
    V                     V  /                          \  V      
[ Object ]              a : A <--------- func ---------> b : B    

```
```n
[Interface]            ta ≈ᴬ ta'<--- trnsPf ---> tb ≈ᴮ tb'
    |                     |            ~            |
    | implements          |           func          |
    V                     |                         |
[abstract]                |                         |
    |                     |                         |
    | inherits            ≡                         ≡
    V                     |                         |
[concrete]                |                         |
    |                     |                         |
    | instantiates        |        Embedding        |
    V                     V            ~            V
[ Object ]             a ≃ᴬ a' <----- path ----> b ≃ᴮ b'

```

## Introduction

### Term

為了能夠紀錄數字的結構，我建立了Term，紀錄包含+, *, C, P, ,! ,Σ ,Π運算

```agda
module Term.Base where

.
.
.

private Idx : Set
Idx = String

data Term {ℓ : Level} (Val : Set ℓ) : Set ℓ where
  `_          : Val → Term Val
  $_          : Idx → Term Val
  _`+_        : Term Val → Term Val → Term Val
  _`*_        : Term Val → Term Val → Term Val
  `Σ[_∈_]_    : Idx → List Val → Term Val → Term Val
  `Π[_∈_]_    : Idx → List Val → Term Val → Term Val
  [_]`!       : Term Val → Term Val
  `P[_,_]     : Term Val → Term Val → Term Val
  `C[_,_]     : Term Val → Term Val → Term Val

```


### Ring 
為了保證提供的Carrier R 與自然數有相同運算結構及性質，其中


```agda
module Ring.Base where

.
.
.

-- Commutative Ring
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R               : Set ℓ
    R0              : R
    R1              : R
    Rhead            : R → R
    Rtail            : R → R
    -- Operations -------------
    _R+_            : R → R → R
    _R*_            : R → R → R   
--    RIdx          : Idx → R
    -- Equivalence relation ----
    _~_             : R → R → Set
    ~-R0            : ∀ (x : R) → Bool
    ~-refl          : ∀ {x : R} → x ~ x
    ~-trans         : ∀ {x y z : R} → x ~ y → y ~ z → x ~ z
    ~-sym           : ∀ {x y : R} → x ~ y → y ~ x
    
    -- head-tail properties ---------
    Rhead-tail       : ∀ (x : R) → (Rhead x R+ Rtail x) ~ x
    Rhead-0h         : ∀ (x : R) → (x ~ R0) → (Rhead x ~ R0)
    Rhead-h0         : ∀ (x : R) → (Rhead x ~ R0) → (x ~ R0)
    Rhead-n0         : ∀ (x : R) → (¬(x ~ R0)) → (Rhead x ~ R1) 
    Rtail-01t        : ∀ (x : R) → ((x ~ R0) ⊎ (x ~ R1)) → (Rtail x ~ R0)
    Rtail-t01        : ∀ (x : R) → (Rtail x ~ R0) → ((x ~ R0) ⊎ (x ~ R1))

    Rhead-~          : ∀ {x y : R} → (x ~ y) → (Rhead x ~ Rhead y)
    Rtail-~          : ∀ {x y : R} → (x ~ y) → (Rtail x ~ Rtail y)
    
    -- Commutative Ring properties ---------  
    R+-identityˡ     : ∀ (x : R)     → (R0 R+ x) ~ x
    R*-identityˡ     : ∀ (x : R)     → (R1 R* x) ~ x
    R+-comm          : ∀ (x y : R)   → (x R+ y) ~ (y R+ x)
    R*-comm          : ∀ (x y : R)   → (x R* y) ~ (y R* x)
    R+-assoc         : ∀ (x y z : R) → ((x R+ y) R+ z) ~ (x R+ (y R+ z))
    R*-assoc         : ∀ (x y z : R) → ((x R* y) R* z) ~ (x R* (y R* z))
    R*-zeroˡ         : ∀ (x : R)     → (R0 R* x) ~ R0
    R*-distribˡ-+    : ∀ (x y z : R) → (x R* (y R+ z)) ~ ((x R* y) R+ (x R* z))
    
    -- Axioms of equality
    R+-axeqˡ         : ∀ (x y z : R)   → x ~ y → (z R+ x) ~ (z R+ y)
    R*-axeqˡ         : ∀ (x y z : R)   → x ~ y → (z R* x) ~ (z R* y)
```


### Eval

這個函數目的是將Term A 還原成 A

```agda
module Term.Eval where

.
.
.

module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring

  private 
    rsigma : List R → (R → R) → R
    rsigma []      F = R0  
    rsigma (i ∷ l) F = (F i) R+ (rsigma l F)

    rpi : List R → (R → R) → R
    rpi []      F = R1  
    rpi (i ∷ l) F = (F i) R* (rsigma l F)

    rC : R → R → R
    {-# NON_TERMINATING #-}
    rC x y with ~-R0 x | ~-R0 y
    ...       | _      | true  = R1
    ...       | true   | _     = R0 
    ...       | _      | _     = (Rhead x R* (rC (Rtail x) (Rtail y))) R+ (rC (Rtail x) (y))

    rP : R → R → R
    {-# NON_TERMINATING #-}
    rP x y with ~-R0 x | ~-R0 y
    ...       | _      | true  = R1
    ...       | true   | _     = R0 
    ...       | _      | _     = x R* (rP (Rtail x) (Rtail y))

    r! : R → R
    r! r =  rP r r 

  infix 1 eval

  {-# NON_TERMINATING #-}
  eval : Term R → R
  eval term with term
  ...          | (` v)            = v
  ...          | ($ i)            = R0   -- not possible
  ...          | (t `+ t₁)        = (eval t) R+ (eval t₁)
  ...          | (t `* t₁)        = (eval t) R* (eval t₁)
  ...          | `P[ t , t₁ ]     = rP (eval t) (eval t₁)
  ...          | `C[ t , t₁ ]     = rC (eval t) (eval t₁)
  ...          | (`Σ[ i ∈ l ] t)  = rsigma l (λ v → eval ([ i := v ] t))
  ...          | (`Π[ i ∈ l ] t)  = rpi l (λ v → eval ([ i := v ] t))
  ...          | [ t ]`!          = r! (eval t)


```







## Evaluator, Translator

```block

ringA ringB : Ring

[Interface]
    Term A -- trns funcAB -> Term B
      |                        |
      |                        |
  eval ringA               eval ringB
      |                        |
      V                        V
      A ------- funcAB ------> B
[concrete]

---------------------------------------------


```

## Embedding

```block
-------------------------------------------

embedAB : Embedding ringA ringB

funcAB = Embedding.EF embedAB


B' = Σ A (Embedding.EF funcAB) -- range of EF


[abstract]   
ringA : Ring --- conv embedAB ---> ringB' : Ring


```

## Translate proof

```block


-------------------------------------------

_≈ᴬ_ : Rel (Term A)
_≈ᴮ_ : Rel (Term B)
_≃ᴬ_ : Rel A
_≃ᴮ_ : Rel B

[Interface]
 ta ≈ᴬ ta' --- trnsPf embedAB ---> tb ≈ᴮ tb'
    |                                 | 
    |                                 |
    ≡                                 ≡
    |                                 |
    V                                 V
  a ≃ᴬ a' ----- path embedAB -----> b ≃ᴮ b'
[concrete]



```



### Files

TremReasoning! 1

Translator!trnsPf 2
N-cal#

CommutativeRing#
EmbeddingConv!conv 1

?path 0

Rings! 7


# Reference


1. [combinational arg.](https://www.google.com/url?sa=t&source=web&rct=j&opi=89978449&url=https://www.math.uvic.ca/faculty/gmacgill/guide/combargs.pdf&ved=2ahUKEwj4yZXLv72HAxU1j68BHVHkAfoQFnoECBQQBg&usg=AOvVaw3yRF1bK4iaNaju-5tZXOop "‌")
2. [](https://en.m.wikipedia.org/wiki/Combinatorial_proof)[![](https://en.wikipedia.org/static/favicon/wikipedia.ico)Combinatorial proof](https://en.m.wikipedia.org/wiki/Combinatorial_proof)
3. [Finite Sets in Homotopy Type Theory](https://cs.ru.nl/~nweide/FiniteSetsInHoTT.pdf "‌")
4. [hott](https://hott.github.io/book/hott-online-15-ge428abf.pdf "‌")
5. [Purely Functional Data Structures](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf "‌")
6. [Formalising Combinatorial Structures and Proof Techniques in Isabelle/HOL](https://api.repository.cam.ac.uk/server/api/core/bitstreams/906a938b-8e26-4d8d-964e-ab77ef4f931b/content#page=61.15 "‌")
7. [Large-Scale Formal Proof for the Working Mathematician—Lessons Learnt from the ALEXANDRIA Project](https://link.springer.com/chapter/10.1007/978-3-031-42753-4_1 "‌")
8. [Cubical Agda: A Dependently Typed Programming Language with Univalence and Higher Inductive Types](https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf "‌")


‌

‌