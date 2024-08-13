# Bridging Combinatorial and Algebraic proof: An Algebraic Approach with Agda

## Abstract

在證明組合恆等式時，有多種不同的方式可以闡述證明，其中包括代數論證和組合論證。組合論證主要依賴於雙重計數（Double counting）和對應論證（bijective proof）兩種技術，前者透過兩種方式構造同一集合來證明恆等式，後者則透過建立兩個集合之間的一一對應來論證。代數論證則依賴於代數運算的特性或定理來證明恆等式。

本文探討如何使用Agda來驗證代數論證與組合論證之間的等價性，通過抽象出兩者的共同代數結構，並證明在Agda中保持這些證明正確性所需的條件，進而建立兩種論證方式之間的等價性 S ≃ S' ↔ n = n'，

#### kws: 
Agda; Commutative ring; Finset; Combinatorial reasoning; Double counting

## Motivation
在學習過程中，組合論證因其直觀的組合意義而更容易理解和構建，而代數證明往往需要通過大量輔助引理的堆砌。為了驗證這兩種證明方法的等價性，本研究希望通過Agda抽象出兩者的共同代數結構，從而系統化地構建組合證明的正確性並探討其等價關係。




ex. ![image](https://hackmd.io/_uploads/ryuXteQq0.png)



## Introduction



## Main frame


### Term, Eval, Trns

```

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

### Term
### Embedding

```
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







```
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


# Agda


## Ring 
為了保證提供的Carrier R 與自然數有相同運算結構及性質，需要證明R/~ 為一交換環，其中為了能構造出C, P, !，會額外要求提供函數Rhead, Rtail，意味著Carrier R存在一種以元素R0為root的樹狀結構，而元素到root的路徑長正為元素的測度(size, length)。


```agda=
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



### Ring Properties

而在上述結構的其他性質

```agda=
module Ring.Properties where

.
.
.


module _ {ℓ : Level} (ring : Ring {ℓ}) where
  open Ring ring  
  
  -- Commutative Ring properties ---------  
  R+-identityʳ : ∀ (x : R) → (x R+ R0) ~ x
  R+-identityʳ x = ~-trans (R+-comm x R0) (R+-identityˡ x)
  
  R*-identityʳ : ∀ (x : R) → (x R* R1) ~ x
  R*-identityʳ x = ~-trans (R*-comm x R1) (R*-identityˡ x)
  
  R*-zeroʳ : ∀ (x : R) → (x R* R0) ~ R0
  R*-zeroʳ x = ~-trans (R*-comm x R0) (R*-zeroˡ x)
  
  -- Axioms of equality
  R+-axeqʳ : ∀ (x y z : R) → x ~ y → (x R+ z) ~ (y R+ z)
  R+-axeqʳ x y z p = ~-trans (R+-comm x z) (~-trans (R+-axeqˡ x y z p) (R+-comm z y))

  R*-axeqʳ : ∀ (x y z : R) → x ~ y → (x R* z) ~ (y R* z)
  R*-axeqʳ x y z p = ~-trans (R*-comm x z) (~-trans (R*-axeqˡ x y z p) (R*-comm z y))
  
  R+-axeq : ∀ (x y s t : R) → x ~ y → s ~ t → (x R+ s) ~ (y R+ t)
  R+-axeq x y s t p q =  ~-trans (R+-axeqʳ x y s p) (R+-axeqˡ s t y q)
  
  R*-axeq : ∀ (x y s t : R) → x ~ y → s ~ t → (x R* s) ~ (y R* t)
  R*-axeq x y s t p q =  ~-trans (R*-axeqʳ x y s p) (R*-axeqˡ s t y q)
 
  -- Commutative Ring properties ---------  
  R*-distribʳ-+ : ∀ (x y z : R) → ((x R+ y) R* z) ~ ((x R* z) R+ (y R* z))
  R*-distribʳ-+ x y z = ~-trans (~-trans (R*-comm (x R+ y) z) (R*-distribˡ-+ z x y) ) (R+-axeq (z R* x) (x R* z) (z R* y) (y R* z) (R*-comm z x) (R*-comm z y))
 
```



## Term

為了能夠紀錄數字的結構，我建立了Term，紀錄包含+, *, Σ ,Π, !, P, C 運算

```agda=
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



### Eval

此函數主要是將一ta : Term A，還原成A中元素，需要提供Carrier R = A 的Ring ringA


```agda=
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

### Trns




```agda=
module Term.Trns where
-- Translate Term A to Term B

open import Term.Base

-- trns : (R → B) → Term R → Term B-----------------------------------------------------------------

infix 1 trns

{-# NON_TERMINATING #-}
trns : {A B : Set} → (A → B) → Term A → Term B
trns func term with term
...               | (` v)            = (` (func v))        
...               | ($ i)            = ($ i)        
...               | (t `+ t₁)        = (trns func t `+ trns func t₁)    
...               | (t `* t₁)        = (trns func t `* trns func t₁)    
...               | `P[ t , t₁ ]     = `P[ trns func t , trns func t₁ ]   
...               | `C[ t , t₁ ]     = `C[ trns func t , trns func t₁ ]   
...               | (`Σ[ i ∈ l ] t)  = (`Σ[ i ∈ map func l ] trns func t)
...               | (`Π[ i ∈ l ] t)  = (`Π[ i ∈ map func l ] trns func t)
...               | [ t ]`!          = [ trns func t ]`!      

```

## Embedding
要轉換證明需要先證明所用的函數是Embedding，即保持運算(Homomorphic)與保持關係。


```agda=
module Ring.EmbeddingConv where

.
.
.

module _ {a b : Level} (rA : Ring {a} ) ( rB : Ring {b}) where
  open Ring

  open import Data.Product
  open import Data.Sum.Base
  -- open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
  open import Ring.Properties
    

  record Embedding : Set (a ⊔ b) where
    field
      -- Homomorphic
      EF : R rA → R rB
      E0 : _~_ rB (EF (R0 rA)) (R0 rB) 
      E1 : _~_ rB (EF (R1 rA)) (R1 rB) 
      Eh : ∀ {x : R rA} → _~_ rB (EF (Rhead rA x)) (Rhead rB (EF x)) 
      Et : ∀ {x : R rA} → _~_ rB (EF (Rtail rA x)) (Rtail rB (EF x)) 
      E+ : ∀ {x y : R rA} → _~_ rB (EF (_R+_ rA x y)) (_R+_ rB (EF x) (EF y)) 
      E* : ∀ {x y : R rA} → _~_ rB (EF (_R*_ rA x y)) (_R*_ rB (EF x) (EF y))

      -- Embedding
      E~ : ∀ {x y : R rA} → _~_ rA x y → _~_ rB (EF x) (EF y) 
  open Embedding    

```



### conv

給定一Embedding，可以利用conv函數建構出Range的Ring structure

```agda=
.
.
.

  private
    A : Set a
    A = R rA
    B : Set b
    B = R rB 
    R0A = R0 rA
    R0B = R0 rB
    R1A = R1 rA
    R1B = R1 rB
    RhA = Rhead rA
    RhB = Rhead rB
    RtA = Rtail rA
    RtB = Rtail rB
    
    _~A_ = _~_ rA
    _~B_ = _~_ rB
    _R+A_ = _R+_ rA
    _R+B_ = _R+_ rB
    _R*A_ = _R*_ rA
    _R*B_ = _R*_ rB

  conv : (Embedding) → Ring {a} → Ring {a ⊔ b}
  conv embd rA = record
    { R               = Σ[ y ∈ B ] Σ[ x ∈ A ] (EF embd x ~B y) 
    ; R0              = R0B , R0A , E0 embd             
    ; R1              = R1B , R1A , E1 embd    
    ; Rhead           = λ (y , x , p) → RhB y , RhA x , ~-trans rB (Eh embd) (Rhead-~ rB p)
    ; Rtail           = λ (y , x , p) → RtB y , RtA x , ~-trans rB (Et embd) (Rtail-~ rB p)
    ; _R+_            = λ (y , x , p) (y' , x' , p') → (y R+B y') , (x R+A x') , ~-trans rB (E+ embd) (R+-axeq rB _ _ _ _ p p')           
    ; _R*_            = λ (y , x , p) (y' , x' , p') → (y R*B y') , (x R*A x') , ~-trans rB (E* embd) (R*-axeq rB _ _ _ _ p p')
    ; _~_             = λ (y , _ , _) (y' , _ , _) → (y ~B y') -- _~B_           
    ; ~-R0            = λ (y , _ , _) → ~-R0 rB y -- isDecEquivR0 rB    
    
    ; ~-refl          = ~-refl rB          
    ; ~-trans         = ~-trans rB         
    ; ~-sym           = ~-sym rB

    ; Rhead-tail      = λ r → Rhead-tail rB (proj₁ r)
    
    ; Rhead-0h        = λ r → Rhead-0h rB (proj₁ r)
    ; Rhead-h0        = λ r → Rhead-h0 rB (proj₁ r) 
    ; Rhead-n0        = λ r f → Rhead-n0 rB (proj₁ r) f  
    ; Rtail-01t       = λ r → Rtail-01t rB (proj₁ r)
    ; Rtail-t01       = λ r → Rtail-t01 rB (proj₁ r) 
     
    ; Rhead-~          = Rhead-~ rB
    ; Rtail-~          = Rtail-~ rB

    ; R+-identityˡ     = λ r → R+-identityˡ rB (proj₁ r)
    ; R*-identityˡ     = λ r → R*-identityˡ rB (proj₁ r)
    ; R+-comm          = λ r r' → R+-comm  rB (proj₁ r) (proj₁ r')
    ; R*-comm          = λ r r' → R*-comm rB (proj₁ r) (proj₁ r')
    ; R+-assoc         = λ r r' r'' → R+-assoc rB (proj₁ r) (proj₁ r') (proj₁ r'')
    ; R*-assoc         = λ r r' r'' → R*-assoc rB (proj₁ r) (proj₁ r') (proj₁ r'')
    ; R*-distribˡ-+    = λ r r' r'' → R*-distribˡ-+ rB (proj₁ r) (proj₁ r') (proj₁ r'') 
    ; R*-zeroˡ         = λ r → R*-zeroˡ rB (proj₁ r)
    ; R+-axeqˡ         = λ r r' r'' p → R+-axeqˡ rB (proj₁ r) (proj₁ r') (proj₁ r'') p
    ; R*-axeqˡ         = λ r r' r'' p → R*-axeqˡ rB (proj₁ r) (proj₁ r') (proj₁ r'') p
    }
```



## Translate proof


# old

```block
-------------------------------------------

embedAB : Embedding ringA ringB

funcAB = Embedding.EF embedAB


B' = Σ A (Embedding.EF funcAB) -- range of EF


[abstract]   
ringA : Ring --- conv embedAB ---> ringB' : Ring


```

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