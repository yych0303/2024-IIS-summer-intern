open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.List.Base 



------ private
private Type = Set
private Type₁ = Set₁



[_]ᶜ : ℕ → List ℕ
[ n ]ᶜ = iterate suc 0 n


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


Pᶜ : ∀ {A : Type} → List A → ℕ → List (List A)
Pᶜ l k = concatMap _!ᶜ (Cᶜ l k)




aa = [ 4 ]ᶜ
-- ac = inserts aa 9
-- bb = aa !ᶜ
cc = Pᶜ aa 3
ll = length cc


fs = [ 5 ]ᶜ
fd = fs !ᶜ
oc = Cᶜ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 3
pc = Cᶜ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 2

 
 