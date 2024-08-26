
  -- ≡ ---
  
  ∈⇒≡ : ∀ {a b : A} 
        → a ∈ [ b ] 
        ------------
        → a ≡ b 

  ≡⇒∈ : ∀ {a b : A} 
        → a ≡ b 
        ------------
        → a ∈ [ b ] 

  -- ∈ ---

  ∈x⇒∈xy : ∀ {a : A} {x y : List A}
            → a ∈ x
            --------------
            → a ∈ (x ++ y)

  ∈y⇒∈xy : ∀ {a : A} {x y : List A}
            → a ∈ y
            ----------------
            → a ∈ (x ++ y)

  -- ∉ ---
  
  ∉-ept : ∀ {a : A} 

          --------
          → a ∉ []

  ∉⇒∉h : ∀ {a b : A} {x : List A} 
          → a ∉ b ∷ x
          ------------ 
          → a ∉ [ b ]
 
  ∉⇒∉t : ∀ {a b : A} {x : List A}
          → a ∉ b ∷ x
          -------------
          → a ∉ x

  ∉∉⇒∉ : ∀ {a : A} {x y : List A}
          → a ∉ x
          → a ∉ y
          --------------
          → a ∉ x ++ y

  ∈xy∉y⇒∈x : ∀ {a : A} {x y : List A}
              → a ∈ x ++ y
              → a ∉ y
              ---------------
              → a ∈ x

  ∈xy∉x⇒∈y : ∀ {a : A} {x y : List A}
              → a ∈ x ++ y
              → a ∉ x
              ------------------
              → a ∈ y

  -- ∈₁ ---

  ∈₁⇒∈ : ∀ {a : A} {x : List A} 
          → a ∈₁ x 
          ---------
          → a ∈ x

  ∈₁x∉y⇒∈₁xy : ∀ {a : A} {x y : List A}
                → a ∈₁ x
                → a ∉ y
                --------------
                → a ∈₁ x ++ y

  ∉x∈₁y⇒∈₁xy : ∀ {a : A} {x y : List A}
                → a ∉ x
                → a ∈₁ y
                --------------
                → a ∈₁ x ++ y

  ∈₁xy∈x⇒∉y : ∀ {a : A} {x y : List A}
                → a ∈₁ x ++ y
                → a ∈ x
                --------------
                → a ∉ y 

  ∈₁xy∈y⇒∉x : ∀ {a : A} {x y : List A}
                → a ∈₁ x ++ y
                → a ∈ y
                ---------------
                → a ∉ x 

  ∈₁xy∉x⇒∈₁y : ∀ {a : A} {x y : List A}
                → a ∈₁ x ++ y
                → a ∉ x 
                --------------
                → a ∈₁ y
