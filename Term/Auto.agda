module Term.Auto where

open import Ring.Base
open import Ring.Properties
open import Term.Base
open import Term.Translate
open import Term.Equiv
open import Term.Evaluate
open import Embedding.Base

open import Agda.Primitive



module _ {a b : Level} {rA : Ring {a}} {rB : Ring {b}} (emb : Embedding rA rB) where
  open Embedding emb
  open Ring rB
  private
    A = Ring.R rA
    B = Ring.R rB




  hat : (t : Term rA) → EF (eval t) ~ evtr emb t
  hat (` x) = ~-refl
--  hat (# n) = EFF  
  hat (t `+ t₁) = ~-trans (E+ (eval t) (eval t₁)) (R+-axeq rB (EF (eval t)) (evtr emb t) (EF (eval t₁)) (evtr emb t₁) (hat t) (hat t₁)) 
  hat (t `* t₁) = ~-trans (E* (eval t) (eval t₁)) (R*-axeq rB (EF (eval t)) (evtr emb t) (EF (eval t₁)) (evtr emb t₁) (hat t) (hat t₁))

  auto : (t t' : Term rA) → t ≈ t' → evtr emb t ~ evtr emb t'
  auto t t' p = ~-trans (~-trans (~-sym (hat t)) (E~ (eval t) (eval t') p)) (hat t') 


  

