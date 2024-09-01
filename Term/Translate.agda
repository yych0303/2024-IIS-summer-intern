module Term.Translate where
-- Translate Term A to Term B

open import Agda.Primitive

open import Term.Base
open import Embedding.Base

-- trns : (R → B) → Term R → Term B-----------------------------------------------------------------

open import Ring.Base

module _ {a b : Level} {rA : Ring {a}} {rB : Ring {b}} (emb : Embedding rA rB) where
  open Embedding emb
  open Ring
  private
    A = R rA
    B = R rB
  
  infix 1 trns

  trns : Term rA → Term rB
  trns term with term
  ...               | (` v)            = (` (EF v))        
--  ...               | ($ i)            = ($ i)        
  ...               | (t `+ t₁)        = (trns t `+ trns t₁)    
  ...               | (t `* t₁)        = (trns  t `* trns t₁)    
--  ...               | `P[ t , t₁ ]     = `P[ trns emb t , trns emb t₁ ]   
--  ...               | `C[ t , t₁ ]     = `C[ trns emb t , trns emb t₁ ]   
--  ...               | (`Σ[ i ∈ l ] t)  = (`Σ[ i ∈ map (EF emb) l ] trns emb t)
--  ...               | (`Π[ i ∈ l ] t)  = (`Π[ i ∈ map (EF emb) l ] trns emb t)
--  ...               | [ t ]`!          = [ trns emb t ]`!      

  
  evtr : Term rA → B
  evtr (` x) = EF x                         
  evtr (t `+ t₁) = _R+_ rB (evtr t) (evtr t₁)   
  evtr (t `* t₁) = _R*_ rB (evtr  t) (evtr t₁)  


