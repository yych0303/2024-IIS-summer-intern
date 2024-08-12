-- {-# OPTIONS --allow-unsolved-metas #-}
module Ring.Properties where

open import Agda.Primitive
open import Ring.Base


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
 