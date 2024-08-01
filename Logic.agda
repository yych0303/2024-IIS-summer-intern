-- {-# OPTIONS --without-K --safe #-}

module Logic where

Type = Set
Type₁ = Set₁

data Bool : Type where
 true false : Bool

-- Type "→" as "\to" or "\->"
not : Bool → Bool
not true  = false
not false = true

idBool : Bool → Bool
idBool x = x

-- Implicit
id : {X : Type} → X → X
id x = x

-- "mix-fix" operator (3rd sense of "_" in Agda)
--                           b      x   y
if_then_else_ : {X : Type} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type)
                 → (b : Bool)
                 → X true
                 → X false
                 → X b
if[ X ] true then  x else y = x
if[ X ] false then x else y = y
