module Eq.KleeneTheory where

open import Prelude
open import T
open import DynTheory
open import HT
open import Eq.Defs

-- Theory about Kleene equality

-- Harper says that Kleene equality is "evidently reflexive",
-- but this requires termination!
kleene-refl : Reflexive KleeneEq
kleene-refl {e} with all-halt e
... | halts eval val = kleeneq _ val eval eval

kleene-sym : Symmetric KleeneEq
kleene-sym (kleeneq n val S1 S2) = kleeneq n val S2 S1

kleene-trans : Transitive KleeneEq
kleene-trans {z = e''} (kleeneq n val e-eval e'-eval) (kleeneq n' val' e'-eval2  e''-eval)
   with eval-deterministic e'-eval e'-eval2 val val'
... | eq = kleeneq _ val e-eval (ID.coe1 (λ x → e'' ~>* x) (symm eq) e''-eval)

kleene-is-equivalence : IsEquivalence KleeneEq
kleene-is-equivalence = record { refl_ = kleene-refl
                               ; sym_ = kleene-sym
                               ; trans_ = kleene-trans }

kleene-converse-evaluation : ∀{e e' d : TNat} →
                             e ≃ e' → d ~>* e → d ≃ e'
kleene-converse-evaluation (kleeneq n val S1 S2) eval =
  kleeneq n val (eval-trans eval S1) S2
