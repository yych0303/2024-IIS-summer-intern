# Translate Term A to Term B

```agda
module Translator where
  
open import Agda.Primitive
open import CommutativeRing public
open import Data.List.Base public
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)

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
