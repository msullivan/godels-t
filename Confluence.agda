-- A generic proof of confluence for a rewriting system with the diamond property.

module Confluence where

open import Prelude

postulate
  Tm : Set
  _=>_ : Tm -> Tm -> Set
  diamond : ∀{M N P : Tm} → (M => N) → (M => P) →
            Σ[ Q :: Tm ] (N => Q × P => Q)


data _=>*_ : Tm → Tm → Set where
  eval-refl : {e : Tm} → e =>* e
  eval-cons : {e e' e'' : Tm} → 
              (S1 : e => e') → (D : e' =>* e'') → e =>* e''

strip : ∀{M N P : Tm} → (M => N) → (M =>* P) →
         Σ[ Q :: Tm ] (N =>* Q × P => Q)
strip S1 eval-refl = , (eval-refl , S1)
strip S1 (eval-cons S2 D) with diamond S1 S2
... | Q' , S1' , S2' with strip S2' D
... | Q , D1 , S' = Q , ((eval-cons S1' D1) , S')

confluence : ∀{M N P : Tm} → (M =>* N) → (M =>* P) →
             Σ[ Q :: Tm ] (N =>* Q × P =>* Q)
confluence eval-refl D2 = , (D2 , eval-refl)
confluence (eval-cons S1 D1) D2 with strip S1 D2
... | M' , D3 , S3 with confluence D1 D3
... | Q , D4 , D4' = Q , D4 , eval-cons S3 D4'
