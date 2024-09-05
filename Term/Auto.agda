module Term.Auto where

open import Ring.Base
open import Ring.Properties
open import Term.Base
open import Term.Translate
-- open import Term.Equiv
open import Term.Evaluate
open import Embedding.Base

open import Agda.Primitive
open import Data.Nat using (ℕ)


module _ {a b : Level} {rA : Ring {a}} {rB : Ring {b}} (emb : Embedding rA rB) (f : ℕ → Ring.R rA) (g : ℕ → Ring.R rB) (EF# : (n : ℕ) → (Ring._~_ rB (Embedding.EF emb (f n)) (g n))) where
  open Embedding emb
  open Ring rB
  private
    A = Ring.R rA
    B = Ring.R rB
    _~A_ = Ring._~_ rA




  hat : (t : Term rA) → EF (eval f t) ~ evtr emb g t
  hat (` x) = ~-refl
  hat (# n) = EF# n  
  hat (t `+ t₁) = ~-trans (E+ (eval f t) (eval f t₁)) (R+-axeq rB (EF (eval f t)) (evtr emb g t) (EF (eval f t₁)) (evtr emb g t₁) (hat t) (hat t₁)) 
  hat (t `* t₁) = ~-trans (E* (eval f t) (eval f t₁)) (R*-axeq rB (EF (eval f t)) (evtr emb g t) (EF (eval f t₁)) (evtr emb g t₁) (hat t) (hat t₁))

  auto : (t t' : Term rA) → (eval f t) ~A (eval f t') → evtr emb g t ~ evtr emb g t'
  auto t t' p = ~-trans (~-trans (~-sym (hat t)) (E~ (eval f t) (eval f t') p)) (hat t') 


  

