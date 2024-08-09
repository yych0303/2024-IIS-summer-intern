# Bridging Combinatorial and Algebraic proof: An Algebraic Approach with Agda

## Abstract



#### kws: 
Commutative ring; Finset; Combinatorial reasoning; Double counting

## Motivation

在證明一個組合恆等式(Combinatorial identity)上會有很多不同的闡述證明的方式，本文主要探討代數論證(Algebraic proof (or argument)）與組合論證（Combinatorial proof (or argument)）

組合論證主要以兩種論證技巧
Double counting: 透過兩種建構方式同一集合來論證恆等式
bijective proof: 建立兩個集合的bijection論證恆等式

代數論證則是透過代數運算的特性或定理論證恆等式

，而在我的求學經驗中組合論證相較於代數論證往往更加簡潔，且易於理解

我關注於兩者背後更深層且共同的代數結構，及建立兩種論證之間的等價 S ≃ S' ↔ n = n'，





ex. ![image](https://hackmd.io/_uploads/ryuXteQq0.png)


## Main frame

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

### Files

TremReasoning! 1

Translator!trnsPf 2
N-cal#

CommutativeRing#
EmbeddingConv!conv 1

?path 0

Rings! 7

## Commutative Ring











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