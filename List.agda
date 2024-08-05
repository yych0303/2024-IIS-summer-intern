open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.List.Base 


open import N-cal
------ private
private Type = Set
private Type₁ = Set₁





-- n 1 → n + 1
inserts : ∀ {A : Type} → List A → A → List (List A)
inserts l a   = reverse (zipWith (λ i → λ t →  i ++ [ a ] ++ t ) (inits l) (tails l))


-- n → n!
_!ᶜ : ∀ {A : Type} → List A → List (List A)
list !ᶜ = helper (reverse list)
    where
        helper : ∀ {A : Type} → List A → List (List A)
        helper [] = [] ∷ []
        helper (x ∷ xs) = concatMap (λ l → inserts l x) (helper xs)


Cᶜ : ∀ {A : Type} → List A → ℕ → List (List A)
Cᶜ _ 0             = [] ∷ []
Cᶜ [] (suc k)      = []
Cᶜ (x ∷ s) (suc k) = map (x ∷_) (Cᶜ s k) ++ (Cᶜ s (suc k))




{- 
evalc : Term ℕ → List (List ℕ)
evalc = eval (record 
  { Ae         = λ x → x
  ; Av         = λ x → [] -- __
  ; _A+_       = _++_
  ; _A*_       = _*_
  ; AC         = Cᶜ
  })
cc = Pᶜ aa 3
ll = length cc


fs = [ 5 ]ᶜ
fd = fs !ᶜ
oc = Cᶜ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 3
pc = Cᶜ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 2

-}



-------------------------------------------------------------------test

  -- sigma x ∈ {2, 3, 4} Cx , 2 = 10
private ev = evalSt (`Σ[ "x"  ∈  (2 ∷ 3 ∷ 4 ∷ []) ] `C[ $ "x" , ` 2 ]  ) 



private er = λ n → λ k → evalSt `C[ ` n `+ ` k , ` k ] 
-- _ = λ n → λ k → `C[ ` n `+ ` k , ` n ]
-- = λ n k → N-cal.combination (n + k) k

-- 0 ~ 4
-- es = evalSt (`Σ[ "x"  ∈  [ 5 ]ᶜ ] ($ "x") ) 

private eee = evalSt (`C[ ` 4 , ` 2 ] ) 
  