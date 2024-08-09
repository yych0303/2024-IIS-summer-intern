# Bridging Combinatorial and Computational Proofs: An Algebraic Approach with Agda

## Abstract


## Motivation

在解一個等式

## Main frame

```n
[Interface]             Term A <-------- trns ---------> Term B    ta ≈ᴬ ta'<--- trnsPf ---> tb ≈ᴮ tb'
    |                     |               ~                |          |            ~            |
    | implements          |              func              |          |           func          |
    V                     |                                |          |                         |
[abstract]                |     Ring   Embedding           |          |                         |
    |                     |       |        |               |          |                         |
    | inherits            |       ∈        ~               |          ≡                         ≡
    V                     |       |        |               |          |                         |
[concrete]              eval <~ ringA <- conv -> ringB ~> eval        |                         |
    |                     |    /                      \    |          |                         |
    | instantiates        |   /                        \   |          |        Embedding        |
    V                     V  /                          \  V          V            ~            V
[ Object ]              a : A <--------- func ---------> b : B     a ≃ᴬ a' <----- path ----> b ≃ᴮ b'

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


在組合學上常常會有證明題會要我們用組合解釋來寫證明
但似乎並不是非常正式（？）的方式
ex. Give a combinatorial argument (no computations are needed) to establish this identity.
我在想會不會有什麼方式可以從
計算證明（or algebraic argument）
isomorphic 到 {以集合論當媒介}
組合證明（combinational argument ）

‌

(S \\cong S') \\cong (Fin n \\cong Fin m) \\to (n = m)


S ≃ S' ↔ n = n'


ref:

1. [combinational arg.](https://www.google.com/url?sa=t&source=web&rct=j&opi=89978449&url=https://www.math.uvic.ca/faculty/gmacgill/guide/combargs.pdf&ved=2ahUKEwj4yZXLv72HAxU1j68BHVHkAfoQFnoECBQQBg&usg=AOvVaw3yRF1bK4iaNaju-5tZXOop "‌")
2. [](https://en.m.wikipedia.org/wiki/Combinatorial_proof)[![](https://en.wikipedia.org/static/favicon/wikipedia.ico)Combinatorial proof](https://en.m.wikipedia.org/wiki/Combinatorial_proof)
3. [Finite Sets in Homotopy Type Theory](https://cs.ru.nl/~nweide/FiniteSetsInHoTT.pdf "‌")
4. [hott](https://hott.github.io/book/hott-online-15-ge428abf.pdf "‌")
5. [Purely Functional Data Structures](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf "‌")
6. [Formalising Combinatorial Structures and Proof Techniques in Isabelle/HOL](https://api.repository.cam.ac.uk/server/api/core/bitstreams/906a938b-8e26-4d8d-964e-ab77ef4f931b/content#page=61.15 "‌")
7. [Large-Scale Formal Proof for the Working Mathematician—Lessons Learnt from the ALEXANDRIA Project](https://link.springer.com/chapter/10.1007/978-3-031-42753-4_1 "‌")
8. [Cubical Agda: A Dependently Typed Programming Language with Univalence and Higher Inductive Types](https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf "‌")

kw:

* Integral Domain ?
* total ordered commutative ring
* hott recursor
* finset
* wholemeal prog. (?)
* comb. reasoning
* The Basic Principle of Counting
* double counting
* [](https://en.wikipedia.org/wiki/Binomial_heap)[![](https://en.wikipedia.org/static/favicon/wikipedia.ico)Binomial heap](https://en.wikipedia.org/wiki/Binomial_heap)
  (?)
* Kuratowski-finite type

‌

例題：

* [](https://www.vaia.com/en-us/textbooks/math/a-first-course-in-probability-9th/combinatorial-analysis/q-111-the-following-identity-is-known-as-fermats-combinatori/)[![](https://website-cdn.studysmarter.de/sites/21/2024/07/StudySmarter-bg-icon.svg)Step by Step Solution](https://www.vaia.com/en-us/textbooks/math/a-first-course-in-probability-9th/combinatorial-analysis/q-111-the-following-identity-is-known-as-fermats-combinatori/)
* [](https://www.chegg.com/homework-help/questions-and-answers/ross-te112-consider-following-combinatorial-identity-sum-k-1-n-k-left-begin-array-l-n-k-en-q101208070)[![](https://cdn.web.chegg.com/static/favicon.ico)Solved (Ross TE1.12) Consider the following combinatorial | Chegg.com](https://www.chegg.com/homework-help/questions-and-answers/ross-te112-consider-following-combinatorial-identity-sum-k-1-n-k-left-begin-array-l-n-k-en-q101208070)

‌

agda:

1. [](https://agda.github.io/agda-stdlib/v1.7.2/Agda.Primitive.html#804)[Agda.Primitive](https://agda.github.io/agda-stdlib/v1.7.2/Agda.Primitive.html#804)
2. [](https://agda.github.io/agda-stdlib/master/Data.Fin.Base.html)[Data.Fin.Base](https://agda.github.io/agda-stdlib/master/Data.Fin.Base.html)
3. [](https://unimath.github.io/agda-unimath/univalent-combinatorics.function-types.html)[![](https://unimath.github.io/agda-unimath/website/images/favicon.svg)Finite function types - agda-unimath](https://unimath.github.io/agda-unimath/univalent-combinatorics.function-types.html)
4. [](https://agda.github.io/cubical/Cubical.Data.FinSet.Base.html)[Cubical.Data.FinSet.Base](https://agda.github.io/cubical/Cubical.Data.FinSet.Base.html)
