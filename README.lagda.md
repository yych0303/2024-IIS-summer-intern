
## Main frame

[Interface]             Term A <-------- trns ---------> Term B    ta ≈ᴬ ta'<--- trnsPf ---> tb ≈ᴮ tb'
    |                     |               ~                |          |            ~            |
    | implements          |              func              |          |         Embedding       |
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