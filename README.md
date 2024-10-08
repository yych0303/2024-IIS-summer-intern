# Bridging Combinatorial and Algebraic proof: An Algebraic Approach with Agda
## Abstract
This research explores the equivalence between algebraic and combinatorial proofs of combinatorial identities using Agda. Combinatorial proofs typically utilize double counting and bijective techniques, while algebraic proofs rely on algebraic operations. The goal is to transform combinatorial proofs into algebraic ones in Agda by abstracting their shared algebraic structure, ensuring proof correctness and equivalence. The equivalence of sets $S$ and $S'$ is expressed as $S \simeq S'$, indicating a bijection, with $S \simeq S' \leftrightarrow n = n'$. This equivalence is crucial in transforming combinatorial proofs into algebraic forms, ensuring the preservation of mathematical accuracy.

**Keywords**: Agda, Commutative ring, Finset, Combinatorial reasoning, Double counting

## Motivation
Combinatorial proofs are often more intuitive and easier to understand due to their reliance on counting and reasoning about sets, which often makes them more accessible. On the other hand, algebraic proofs, while more formal, typically require the buildup of numerous auxiliary lemmas and the use of more complex mathematical tools such as calculus and generating functions. This complexity can make proving intricate combinatorial identities in Agda a challenging task.

This research aims to verify the equivalence of these two proof methods by abstracting their common algebraic structure in Agda, thereby systematically constructing the correctness of combinatorial proofs and exploring their equivalence. By establishing this equivalence, this study hopes to provide a new dimension of proof that could bridge the gap between combinatorial and algebraic approaches.

## 0 Intoduction



### 0.1 Combinatorial Operators of Interest
Combinatorial operators are crucial tools in combinatorics for constructing, manipulating, or analyzing combinatorial objects. These operators help describe the properties of combinatorial structures, calculate combinatorial numbers, or analyze other combinatorial phenomena.

1. **`+` : Addition and `*` Multiplication Operators**: These are common in calculating combinatorial numbers, used to combine or expand combinatorial objects.
2. **`Σ` : Summation of a Sequence** Summation operator, which aggregates a list of elements by summing them according to a given function.
3. **`Π` : Product of a Sequence** Multiplication operator, which aggregates a list of elements by multiplying them according to a given function.
4. **`P` : Permutation Operator**: These handle or manipulate the permutations of a set of elements, where a permutation can be seen as a combinatorial operation.
5. **`C` : Selection Operator**: These describe how to select subsets from a set, such as choosing k elements from n elements.
6. **`!` : Factorial** Which is a specific case of permutation.


### 0.2 Example of Combinatorial and Algebraic proof




![image](https://hackmd.io/_uploads/H1-32sRj0.png)


#### (a) Combinatorial Argument

To prove this identity combinatorially, we can consider the problem of selecting a committee from a group of $n$ people, where one person in the committee is chosen as the chairperson.

- **(i) Number of possible selections for a committee of size $k$ and its chairperson:**

  - First, choose $k$ members out of $n$. This can be done in $\binom{n}{k}$ ways.
  - Then, choose the chairperson from the $k$ members of the committee. This can be done in $k$ ways.
  
  Therefore, the total number of ways to choose a committee of size $k$ with a chairperson is $k \cdot \binom{n}{k}$.
  
- **(ii) Number of possible selections of a chairperson and the other committee members:**

  - Select the chairperson from the $n$ people. This can be done in $n$ ways.
  - After choosing the chairperson, the remaining $n-1$ people can either be included in the committee or not. This gives $2^{n-1}$ possible subsets.
  
  Therefore, the total number of ways to choose the chairperson and the other committee members is $n \cdot 2^{n-1}$.

Since these two counts represent the same situation, the identity is proven combinatorially.

#### (b) Algebraic Argument

To prove the identity algebraically, use the binomial theorem:

$$
(1 + x)^n = \sum_{k=0}^n \binom{n}{k} x^k
$$

Differentiate both sides with respect to $x$:

$$
n(1 + x)^{n-1} = \sum_{k=1}^n k \binom{n}{k} x^{k-1}
$$

Now, set $x = 1$:

$$
n \cdot 2^{n-1} = \sum_{k=1}^n k \binom{n}{k}
$$

This gives the desired identity.

### 0.3 Summary of Example Proofs:
**Comparison:**
- The combinatorial proof is intuitive, relying on counting and reasoning about sets, which often makes it easier to understand.
- The algebraic proof uses a more formal, symbolic approach by manipulating algebraic expressions and applying theorems such as the binomial theorem.

In the context of the research, the goal is to abstract the common algebraic structure underlying these proofs and verify their equivalence within Agda, thus demonstrating that both approaches are valid and equivalent in proving the same combinatorial identity.




## 1 Algebraic Structure of Combinatorial Systems


### 1.1 Algebraic Structure: `Ring`

The algebraic structure `Ring` is defined as a record in Agda that captures the essential operations, identities, equivalence relations, and properties of a ring. Here's a 

#### 1. Carrier `R : Set`

#### 2. Operations
- `_R+_` **Addition**:
  This operation represents the addition of two elements within the ring R.
- `_R*_` **Multiplication**: 
  This operation represents the multiplication of two elements within the ring R.
- `Rhead` **Head**: 
  This function is defined to retrieve or manipulate the "head" of an element in R, playing a role in decomposing elements.
- `Rtail` **Tail**: 
  This function is defined to retrieve or manipulate the "tail" of an element in R, complementing the head function.

#### 3. Equivalence Relation
- **Relation**: `_~_`  
  An equivalence relation `_~_` defined on the elements of R, ensuring reflexivity, transitivity, and symmetry.

#### 4. Identities
- `R0` **Zero**:   
  The additive identity, satisfying R0 R+ x ~ x for any element x.
- `R1` **One**:   
  The multiplicative identity, satisfying R1 R* x ~ x for any element x.

#### 5. Constraints on Operations

- **head-tail properties**: 
- **Commutative ring properties**
    - **Identity**: 
    - **Commutativity**: Both addition and multiplication are commutative.
    - **Associativity**: Both addition and multiplication are associative.
    - **Distributivity**: Multiplication distributes over addition.
- **Axiom of Equality**: Ensures that equivalence is preserved under addition and multiplication.


#### Theorem
- R/~ is a commutative integral domain. 
  This theorem states that the quotient of carrier `R` under the equivalence relation `_~_` forms a commutative integral domain, meaning it has no zero divisors and is commutative under both addition and multiplication.

#### Agda Code for Ring Definition

Here is the Agda code that defines the `Ring` record with the above properties:

```agda=
record Ring {ℓ : Level} : Set (lsuc ℓ) where
  field
    R               : Set ℓ
    R0              : R
    R1              : R
    Rhead           : R → R
    Rtail           : R → R
    -- Operations -------------
    _R+_            : R → R → R
    _R*_            : R → R → R   
    -- Equivalence relation ----
    _~_             : R → R → Set
    ~-R0            : ∀ (x : R) → Bool
    ~-refl          : ∀ {x : R} → x ~ x
    ~-trans         : ∀ {x y z : R} → x ~ y → y ~ z → x ~ z
    ~-sym           : ∀ {x y : R} → x ~ y → y ~ x

    -- head-tail properties ---------
    Rhead-tail      : ∀ (x : R) → (Rhead x R+ Rtail x) ~ x
    Rhead-0h        : ∀ (x : R) → (x ~ R0) → (Rhead x ~ R0)
    Rhead-h0        : ∀ (x : R) → (Rhead x ~ R0) → (x ~ R0)
    Rhead-n0        : ∀ (x : R) → (¬(x ~ R0)) → (Rhead x ~ R1) 
    Rtail-01t       : ∀ (x : R) → ((x ~ R0) ⊎ (x ~ R1)) → (Rtail x ~ R0)
    Rtail-t01       : ∀ (x : R) → (Rtail x ~ R0) → ((x ~ R0) ⊎ (x ~ R1))

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

This code formalizes the definition of a ring with all its essential operations and constraints, ensuring that it adheres to the axioms of ring theory and can be used for rigorous algebraic reasoning in Agda.


### 1.2 Additional Properties of R

In the algebraic structure R, additional properties and axioms are defined to further characterize the behavior of operations, particularly in the context of commutative rings. These properties ensure that operations behave consistently and satisfy fundamental algebraic laws. Below is a detailed explanation of these properties and their corresponding Agda code.

#### Additional Commutative Ring Properties

- **Right Identity for Addition**: \( R+\-identityʳ \)
  - This property ensures that adding the identity element \( R0 \) to any element \( x \) on the right results in \( x \) itself.
  - **Agda Definition**:
    ```agda=
    R+-identityʳ : ∀ (x : R) → (x R+ R0) ~ x
    R+-identityʳ x = ~-trans (R+-comm x R0) (R+-identityˡ x)
    ```

- **Right Identity for Multiplication**: \( R*-identityʳ \)
  - This property ensures that multiplying any element \( x \) by the identity element \( R1 \) on the right results in \( x \) itself.
  - **Agda Definition**:
    ```agda=
    R*-identityʳ : ∀ (x : R) → (x R* R1) ~ x
    R*-identityʳ x = ~-trans (R*-comm x R1) (R*-identityˡ x)
    ```

- **Right Zero for Multiplication**: \( R*-zeroʳ \)
  - This property ensures that multiplying any element \( x \) by the zero element \( R0 \) on the right results in \( R0 \).
  - **Agda Definition**:
    ```agda=
    R*-zeroʳ : ∀ (x : R) → (x R* R0) ~ R0
    R*-zeroʳ x = ~-trans (R*-comm x R0) (R*-zeroˡ x)
    ```

#### Axioms of Equality

- **Right Equality for Addition**: \( R+\-axeqʳ \)
  - Ensures that if \( x \sim y \), then \( x + z \sim y + z \).
  - **Agda Definition**:
    ```agda=
    R+-axeqʳ : ∀ (x y z : R) → x ~ y → (x R+ z) ~ (y R+ z)
    R+-axeqʳ x y z p = ~-trans (R+-comm x z) (~-trans (R+-axeqˡ x y z p) (R+-comm z y))
    ```

- **Right Equality for Multiplication**: \( R*-axeqʳ \)
  - Ensures that if \( x \sim y \), then \( x * z \sim y * z \).
  - **Agda Definition**:
    ```agda=
    R*-axeqʳ : ∀ (x y z : R) → x ~ y → (x R* z) ~ (y R* z)
    R*-axeqʳ x y z p = ~-trans (R*-comm x z) (~-trans (R*-axeqˡ x y z p) (R*-comm z y))
    ```

- **Combined Equality for Addition**: \( R+\-axeq \)
  - Ensures that if \( x \sim y \) and \( s \sim t \), then \( x + s \sim y + t \).
  - **Agda Definition**:
    ```agda=
    R+-axeq : ∀ (x y s t : R) → x ~ y → s ~ t → (x R+ s) ~ (y R+ t)
    R+-axeq x y s t p q =  ~-trans (R+-axeqʳ x y s p) (R+-axeqˡ s t y q)
    ```

- **Combined Equality for Multiplication**: \( R*-axeq \)
  - Ensures that if \( x \sim y \) and \( s \sim t \), then \( x * s \sim y * t \).
  - **Agda Definition**:
    ```agda=
    R*-axeq : ∀ (x y s t : R) → x ~ y → s ~ t → (x R* s) ~ (y R* t)
    R*-axeq x y s t p q =  ~-trans (R*-axeqʳ x y s p) (R*-axeqˡ s t y q)
    ```

#### Distributive Properties

- **Right Distributivity of Multiplication over Addition**: \( R*-distribʳ-+ \)
  - This property ensures the distributive law for multiplication over addition holds when multiplication is applied on the right side of the addition.
  - **Agda Definition**:
    ```agda=
    R*-distribʳ-+ : ∀ (x y z : R) → ((x R+ y) R* z) ~ ((x R* z) R+ (y R* z))
    R*-distribʳ-+ x y z = ~-trans (~-trans (R*-comm (x R+ y) z) (R*-distribˡ-+ z x y) )
                          (R+-axeq (z R* x) (x R* z) (z R* y) (y R* z) (R*-comm z x) (R*-comm z y))
    ```

#### Summary

These additional properties extend the basic algebraic structure of \( R \), reinforcing that it adheres to the principles of a commutative ring with respect to addition and multiplication. The axioms of equality ensure consistent behavior when comparing elements, and the distributive property guarantees that multiplication distributes over addition, which is essential for maintaining the integrity of the ring structure. The Agda code provided formalizes these properties, enabling rigorous reasoning about the structure within a proof assistant environment.

### 1.3 Definition of Combinatorial Operations

In this context, combinatorial operations are defined using recursive functions that leverage the algebraic structure \( R \). Below are the definitions of key combinatorial operations such as summation, multiplication, binomial coefficients, permutations, and factorials.

#### Operations

- **Sigma**: Summation operator, which aggregates a list of elements by summing them according to a given function.
- **Product**: Multiplication operator, which aggregates a list of elements by multiplying them according to a given function.
- **C**: Binomial coefficient, representing the number of ways to choose \( y \) elements from a set of \( x \) elements.
- **P**: Permutation count, representing the number of ways to arrange \( y \) elements from a set of \( x \) elements.
- **!**: Factorial, which is a specific case of permutation count where \( y = x \).

#### Agda Code for Combinatorial Operations

The following Agda code defines these operations within the algebraic structure \( R \):

```agda=
rsigma : List R → (R → R) → R
rsigma []      F = R0  
rsigma (i ∷ l) F = (F i) R+ (rsigma l F)

rpi : List R → (R → R) → R
rpi []      F = R1  
rpi (i ∷ l) F = (F i) R* (rpi l F)

rC : R → R → R
{-# NON_TERMINATING #-}
rC x y with ~-R0 x | ~-R0 y
...       | _      | true  = R1
...       | true   | _     = R0 
...       | _      | _     = (Rhead x R* (rC (Rtail x) (Rtail y))) R+ (rC (Rtail x) y)

rP : R → R → R
{-# NON_TERMINATING #-}
rP x y with ~-R0 x | ~-R0 y
...       | _      | true  = R1
...       | true   | _     = R0 
...       | _      | _     = x R* (rP (Rtail x) (Rtail y))

r! : R → R
r! r = rP r r
```

#### Explanation

1. **`rsigma`**:
   - The function `rsigma` recursively sums elements of a list. If the list is empty, it returns the additive identity \( R0 \). Otherwise, it applies the function \( F \) to the first element and adds it to the result of recursively summing the rest of the list.

2. **`rpi`**:
   - The function `rpi` recursively multiplies elements of a list. If the list is empty, it returns the multiplicative identity \( R1 \). Otherwise, it applies the function \( F \) to the first element and multiplies it with the result of recursively multiplying the rest of the list.

3. **`rC`**:
   - The function `rC` calculates the binomial coefficient, \( C(x, y) \), using a recursive formula. It handles the base cases where either \( x \) or \( y \) is zero, and for other cases, it recursively computes the combination using the head and tail of the elements.

4. **`rP`**:
   - The function `rP` calculates the permutation count, \( P(x, y) \), using a recursive formula similar to `rC`. It also handles base cases where either \( x \) or \( y \) is zero.

5. **`r!`**:
   - The factorial function `r!` is defined as a specific case of `rP`, where \( x \) and \( y \) are the same. It effectively counts the number of ways to arrange the elements in the set.

These functions provide a framework for performing combinatorial operations within the algebraic structure \( R \), preserving the properties and relationships essential for combinatorial reasoning.

### 1.4 ringN

```agda=


ringℕ : Ring
ringℕ = record
  { R               = ℕ        
  ; R0              = 0        
  ; R1              = 1          
  ; _R+_            = _+_        
  ; _R*_            = _*_            
  ; Rhead           = rh   
  ; Rtail           = rt       
  ; _~_             = _≡_     
  ; ~-R0            = λ { 0 → true ; _ → false }    
  ; ~-refl          = refl          
  ; ~-trans         = trans         
  ; ~-sym           = sym 
  ; Rhead-tail      = ht
  ; Rhead-0h        = 0h 
  ; Rhead-h0        = h0
  ; Rhead-n0        = hn0 
  ; Rtail-01t       = 01t 
  ; Rtail-t01       = t01
  ; Rhead-~         = λ p → cong rh p  
  ; Rtail-~         = λ p → cong rt p  
  ; R+-identityˡ    = λ x → refl
  ; R*-identityˡ    = *-identityˡ
  ; R+-comm         = +-comm
  ; R*-comm         = *-comm
  ; R+-assoc        = +-assoc
  ; R*-assoc        = *-assoc
  ; R*-zeroˡ        = λ x → refl
  ; R*-distribˡ-+   = *-distribˡ-+ 
  ; R+-axeqˡ        = +ae
  ; R*-axeqˡ        = *ae
  }
    where
      rh : ℕ → ℕ
      rh 0       = 0
      rh (suc x) = 1  
      rt : ℕ → ℕ
      rt 0       = 0
      rt (suc x) = x  

      ht : (x : ℕ) → rh x + rt x ≡ x
      ht zero = refl
      ht (suc x) = refl

      0h : (x : ℕ) → (x ≡ 0) → (rh x ≡ 0)
      0h 0 = λ p → cong rh p
      0h (suc x) = λ p → cong rh p
      h0 : (x : ℕ) → (rh x ≡ 0) → (x ≡ 0)
      h0 0 = λ p → refl
      h0 (suc x) = λ p → ⊥-elim (contradiction p)
        where
          contradiction : 1 ≡ 0 → ⊥
          contradiction ()
      hn0 : (x : ℕ) → ¬ (x ≡ 0) → rh x ≡ 1
      hn0 zero = λ x → ⊥-elim (x refl)
      hn0 (suc x) = λ _ → refl
      
      contradiction : (x : ℕ) → suc (suc x) ≡ 1 → ⊥
      contradiction zero = λ () 
      contradiction (suc x) = λ ()    
      proof : (x : ℕ) → suc x ≡ 1 → x ≡ 0
      proof 0 p = refl
      proof (suc x) p = ⊥-elim (contradiction x p)
      tof : (x : ℕ) → (suc x ≡ 0 ⊎ suc x ≡ 1 → x ≡ 0)
      tof x (_⊎_.inj₂ y) = proof x y


      01t : (x : ℕ) → ((x ≡ 0) ⊎ (x ≡ 1)) → (rt x ≡ 0)

      01t zero    = λ p → refl
      01t (suc x) = tof x 

      t01 : (x : ℕ) → (rt x ≡ 0) → ((x ≡ 0) ⊎ (x ≡ 1))
      
      t01 zero = λ p → _⊎_.inj₁ refl
      t01 (suc x) = λ p → _⊎_.inj₂ (cong suc p)
      
      +ae : ∀ (x y z : ℕ) → x ≡ y → (z + x) ≡ (z + y)
      +ae _ _ z p = cong (z +_) p
      *ae : ∀ (x y z : ℕ) → x ≡ y → z * x ≡ z * y
      *ae _ _ z p = cong (z *_) p
 

```
## 2 FinSet

### 2.1 Membership of List


### 2.2 Properties of membership

### 2.3 FinSet

### 2.4 ringFinSet


## 3 Embedding Functions
### 3.1 Embedding
In this context, embedding functions and their properties are crucial for preserving the structure of operations during the transition from one domain to another. Here’s a breakdown:

- **Embedding Function (EF)**: The embedding function \( EF \) maps elements from one structure into another, ensuring that the essential properties and operations are preserved during the embedding process.

- **Identity Mapping**: The identity elements must be preserved under the embedding function. Specifically:
  - \( E0 \): The identity element for addition maps to the identity element for addition in the embedded structure.
  - \( E1 \): The identity element for multiplication maps to the identity element for multiplication in the embedded structure.

- **Homomorphisms**: The operations within the structure are preserved by the corresponding homomorphisms under embedding:
  - \( E+ \): Represents the preservation of the addition operation under embedding.
  - \( E* \): Represents the preservation of the multiplication operation under embedding.
  - \( Eh \): Represent the preservation of the head operation (if applicable) under embedding.
  - \( Et \): Represent the preservation of the tail operation (if applicable) under embedding.

- **Structure Preservation (E~)**: The equivalence relations and structural properties of the original structure are maintained under the embedding. This ensures that the embedded structure is isomorphic or homomorphic to the original, depending on the context and the operations involved.

This formalization of embedding functions ensures that the algebraic and combinatorial properties being studied remain consistent and meaningful across different structures and domains in the research.

#### Agda Code for `Embedding`:

```agda=
record Embedding : Set (a ⊔ b) where
  field
    -- Homomorphic properties
    EF  : R rA → R rB
    E0  : _~_ rB (EF (R0 rA)) (R0 rB)
    E1  : _~_ rB (EF (R1 rA)) (R1 rB)
    Eh  : ∀ (x : R rA) → _~_ rB (EF (Rhead rA x)) (Rhead rB (EF x))
    Et  : ∀ (x : R rA) → _~_ rB (EF (Rtail rA x)) (Rtail rB (EF x))
    E+  : ∀ (x y : R rA) → _~_ rB (EF (_R+_ rA x y)) (_R+_ rB (EF x) (EF y))
    E*  : ∀ (x y : R rA) → _~_ rB (EF (_R*_ rA x y)) (_R*_ rB (EF x) (EF y))

    -- Structure preservation
    E~  : ∀ (x y : R rA) → _~_ rA x y → _~_ rB (EF x) (EF y)
  open Embedding
```

This code defines an `Embedding` record that captures the essential properties needed to maintain the algebraic structure during embedding. Each field represents a key aspect of homomorphism or structure preservation, ensuring that the embedded structure accurately reflects the original.


### 3.2 Embedding from FinSet to N !



### 3.3 Conversion of Rings via Embedding

The `conv` function is designed to generate the algebraic structure formed by the image of the embedding function `EF`. This process involves mapping elements through `EF` and then studying the resulting structure within the new domain, ensuring that it retains the necessary algebraic properties derived from the original ring. This approach is crucial for analyzing how the original ring structure transforms under embedding and how its operations and identities are preserved in the new context.

Here is the Agda code for the `conv` function:

```agda=
conv : (Embedding rA rB) → Ring {a} → Ring {a ⊔ b}
conv embd rA = record
  { R               = Σ[ y ∈ B ] Σ[ x ∈ A ] (EF embd x ~B y) 
  ; R0              = R0B , R0A , E0 embd             
  ; R1              = R1B , R1A , E1 embd    
  ; Rhead           = λ (y , x , p) → RhB y , RhA x , ~-trans rB (Eh embd x) (Rhead-~ rB p)
  ; Rtail           = λ (y , x , p) → RtB y , RtA x , ~-trans rB (Et embd x) (Rtail-~ rB p)
  ; _R+_            = λ (y , x , p) (y' , x' , p') → (y R+B y') , (x R+A x') , ~-trans rB (E+ embd x x') (R+-axeq rB _ _ _ _ p p')           
  ; _R*_            = λ (y , x , p) (y' , x' , p') → (y R*B y') , (x R*A x') , ~-trans rB (E* embd x x') (R*-axeq rB _ _ _ _ p p')
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

#### Explanation

- **Ring Operations and Identity Mapping**: The `conv` function constructs a new ring structure by mapping elements from `rA` to `rB` via the embedding function `EF`. It ensures that the identity elements (`R0`, `R1`) and operations (`R+`, `R*`) are preserved in the new domain.

- **Structure Preservation**: The fields `E0`, `E1`, `E+`, `E*`, `Eh`, and `Et` in the `Embedding` record ensure that the operations and identities from the original ring are preserved in the embedded structure. This preservation is critical for maintaining the algebraic integrity of the embedded structure.

- **Equivalence Relation**: The equivalence relation `~` is also preserved under embedding, ensuring that if two elements are equivalent in the original ring, their images under the embedding function will be equivalent in the new ring.

This code formalizes the transformation of a ring structure through embedding, ensuring that all algebraic properties and operations are preserved in the new context, which is crucial for maintaining the consistency of the algebraic framework across different domains.

## 4 Examples of Transforming a Proof

### 4.1 Commutativity of Addition

The goal is to prove the commutativity of addition, \( n + m = m + n \), by using a transformed proof involving the embedding function \( EF \) and the operations on finite sets.

#### Agda Code

The first proof, `combi-pf`, establishes the equivalence of the structures after applying the `R+` operation to finite sets `F n` and `F m`:

```agda=
combi-pf : (n m : ℕ) → ((F n) R+ (F m)) ~ ((F m) R+ (F n))
combi-pf n m = record { to   = λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y} 
                      ; from =  λ {(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
                      ; from∘to = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                      ; to∘from = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                      }
```

The second proof, `algeb-pf`, uses the `combi-pf` to demonstrate the commutativity of addition:

```agda=
algeb-pf : (n m : ℕ) → n + m ≡ m + n 
algeb-pf n m = 
  begin 
    n + m
  ≡⟨ sym (cong₂ _+_ (EFF n) (EFF m)) ⟩
    EF (F n) + EF (F m)
  ≡⟨ sym (E+ (F n) (F m)) ⟩
    EF ((F n) R+ (F m))
  ≡⟨ E~ ((F n) R+ (F m)) ((F m) R+ (F n)) (combi-pf n m)  ⟩
    EF ((F m) R+ (F n))
  ≡⟨ E+ (F m) (F n) ⟩
    EF (F m) + EF (F n)
  ≡⟨ cong₂ _+_ (EFF m) (EFF n) ⟩
    m + n  
  ∎
```
#### Explanation from the Middle of the Proof

The goal is to prove the commutativity of addition $n + m = m + n$ by leveraging the properties of the `Embedding` structure and the embedding function `EF`. Here's how the proof works from the middle, focusing on the use of `E~`, homomorphism `E+`, and `EFF`.

##### **1. Using `E~`:**
`E~` is a field of the `Embedding` record, which ensures that the equivalence relation \( \sim \) is preserved under the embedding function `EF`. Specifically, if two elements `x` and `y` are equivalent in the original structure (i.e., `x ~ y`, then their images under `EF` are also equivalent in the embedded structure (i.e., `EF(x) ~ EF(y)`).

In the proof:
- The goal is to show that `EF((F n) R+ (F m)) ≡ EF((F m) R+ (F n))`.
- The function `E~` is used to transform the equivalence in the original domain `(F n) R+ (F m) ~ (F m) R+ (F n)` into an equivalence in the embedded domain `EF((F n) R+ (F m)) ≡ EF((F m) R+ (F n))`.

##### **2. Using Homomorphism `E+`:**
The field `E+` in the `Embedding` record ensures that the addition operation `R+` is preserved under the embedding function `EF`. Specifically, if `x` and `y` are elements in the original structure, then:
`EF(x R+ y) ~ EF(x) R+ EF(y)`
This property is used to show that the embedding of the sum `(F n) R+ (F m) ` corresponds to the sum of the embeddings `EF(F n) + EF(F m)`.

In the proof:
- After applying `E~`, `E+` is used to move from the embedded operation back to the sum of the individual embedded elements, i.e., \( EF((F n) R+ (F m)) \sim EF(F n) + EF(F m) \).

##### **3. Using `EFF`:**
`EFF` refers to a function or property that establishes a direct relationship between the embedding function `EF` and the original elements \( F n \). It essentially states that embedding \( F n \) using `EF` returns \( n \):
\[ EF(F n) = n \]
This property is crucial for returning to the original numeric domain after applying the embedding.

In the proof:
- Once the equivalence \( EF(F n) + EF(F m) \sim EF(F m) + EF(F n) \) has been established using `E+` and `E~`, `EFF` is applied to simplify \( EF(F n) \) and \( EF(F m) \) back to \( n \) and \( m \), respectively.
- This yields \( n + m = m + n \), completing the proof of commutativity.

#### Summary
The proof leverages the properties of the `Embedding` structure, particularly the preservation of operations and equivalence relations through `E+`, `E~`, and `EFF`, to demonstrate that the commutativity of addition \( n + m = m + n \) holds by transforming and analyzing the operations within the embedded structure.

### 4.2 Associativity of Product

#### Agda code

```agda=
combi-pf2 : (n m l : ℕ) → ((F n) R* ((F m) R* (F l))) ~ (((F n) R* (F m)) R* (F l))
combi-pf2 n m l = record { to   = λ {(i , (j , k)) → ((i , j) , k)} 
                      ; from = λ {((i , j) , k) → (i , (j , k))}
                      ; from∘to = λ {(i , (j , k)) → refl}
                      ; to∘from = λ {((i , j) , k) → refl}
                      }


algeb-pf2 : (n m l : ℕ) → n * (m * l) ≡ (n * m) * l 
algeb-pf2 n m l = 
  begin 
    n * (m * l)
  ≡⟨ sym (cong (_* (m * l)) (EFF n)) ⟩
    EF (F n) * (m * l)
  ≡⟨ sym (cong (EF (F n) *_) (cong₂ _*_ (EFF m) (EFF l))) ⟩
    EF (F n) * (EF (F m) * EF (F l))
  ≡⟨ sym (cong (EF (F n) *_) (E* (F m) (F l))) ⟩
    EF (F n) * EF ((F m) R* (F l))
  ≡⟨ sym (E* (F n) ((F m) R* (F l))) ⟩
    EF ((F n) R* ((F m) R* (F l)))
  ≡⟨ E~ ((F n) R* ((F m) R* (F l))) (((F n) R* (F m)) R* (F l)) (combi-pf2 n m l)  ⟩
    EF (((F n) R* (F m)) R* (F l))
  ≡⟨ E* (((F n) R* (F m))) ((F l)) ⟩
    EF ((F n) R* (F m)) * EF (F l)
  ≡⟨ cong (_* EF (F l)) (E* (F n) (F m)) ⟩
    (EF (F n) * EF (F m)) * EF (F l)
  ≡⟨ cong (_* EF (F l)) (cong₂ _*_ (EFF n) (EFF m)) ⟩
    (n * m) * EF (F l)
  ≡⟨ cong ((n * m) *_) (EFF l) ⟩
    (n * m) * l
  ∎

```



## 5 Term !

### 5.1 term
### 5.2 Eval
### 5.3 example of term

## Unfinished Code Components
1. inject-∈ Function
2. ringFinSet Implementation
3. embdFinSet Implementation Eh, Et
## Future Studies

### 1. **Automatic Proof Generation Using `data Term`**

Future research can focus on automating proof generation using the `data Term` structure. This approach involves abstracting combinatorial and algebraic operations as terms within a formal system. By defining these operations as `data Term`, one can automate the reasoning and proof generation process in Agda. This would allow for the automatic verification of complex identities and the transformation of combinatorial proofs into algebraic forms (or vice versa) without extensive manual intervention.

### 2. **Additional Operations to Implement**

In the context of expanding the algebraic and combinatorial framework, the following operations should also be considered for implementation:

- **Minus (−)**: Represents the subtraction operation. It is essential to define this operation within the algebraic structure to handle differences between combinatorial quantities.

- **Divided (÷)**: Represents division, which can be used to express ratios or to divide one combinatorial quantity by another.

- **Power (A^B)**: Represents exponentiation, where a base \( A \) is raised to the power of \( B \). This operation is common in combinatorial settings, such as counting functions or combinations with repetition.

- **Conditioned Subset \(\{A \mid \phi\}\)**: Represents the subset of \( A \) that satisfies a condition \( \phi \). This operation is crucial in combinatorial proofs, where subsets are often defined by specific properties or conditions. Implementing this operation involves handling logical conditions within the set structure.

These extensions to the `data Term` structure will allow for more comprehensive coverage of combinatorial and algebraic operations, facilitating more powerful automated reasoning capabilities within Agda.

### 3. **Category Theory Perspective**

When viewed from a category theory perspective, the algebraic operations and combinatorial structures can be interpreted as categorical constructs:

- **`R+`**: 

- **`R*`**: This operation is seen as function composition $f \circ g$. In category theory, composition is fundamental, representing the chaining of morphisms (functions) from one object to another, capturing the idea of multiplication in an algebraic sense.

- **`P(A, B)`**: This represents an injection function from \( B \) to \( A \). In categorical terms, this could be seen as a monomorphism, where the injection preserves the structure of \( B \) within \( A \).

- **`C(A, B)`**: This represents a monotonic injection function, which could be interpreted as a morphism that preserves a specific order or structure from \( B \) to \( A \). This could correspond to an order-preserving map in a category of posets or a similar structure.

By interpreting these operations through the lens of category theory, you can leverage categorical constructs to better understand and formalize the relationships between algebraic and combinatorial proofs. This approach may also provide deeper insights into the nature of these operations and how they interact within the broader framework of your research.


## Conclusion
Conclusion:

By abstracting set theory and arithmetic structures in number theory, this research has constructed a promising system. It is believed that once the automation of the Term is completed, this system will provide a new pathway for proof methods in Agda, lowering the difficulty and technical barrier of proofs while increasing their readability. However, due to time constraints, there are still many parts of the project that remain unfinished, including the proof of `once` in FinSet multiplication and the Lemma `inject-∈` used for defining addition.

## References

- FRUMIN, Dan, et al. "Finite sets in homotopy type theory." *Proceedings of the 7th ACM SIGPLAN International Conference on Certified Programs and Proofs*. 2018. pp. 201-214.

- EDMONDS, Chelsea. *Formalising Combinatorial Structures and Proof Techniques in Isabelle/HOL*. 2024. PhD Thesis.

- RIJKE, Egbert; SPITTERS, Bas. "Sets in homotopy type theory." *Mathematical Structures in Computer Science*. 2015, 25(5): 1172-1202.

- The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. arXiv preprint arXiv:1308.0729, 2013.
