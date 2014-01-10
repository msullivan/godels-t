-- I decided that I wanted my Eq development to be separate from my HT one,
-- which means that I prove Kleene is reflexive through logical equivalence
-- being reflexive

module Eq.KleeneTheoryEarly where

open import Prelude
open import T
open import DynTheory
open import Eq.Defs

-- Theory about Kleene equality

kleene-sym : Symmetric KleeneEq
kleene-sym (kleeneq n val S1 S2) = kleeneq n val S2 S1

kleene-trans : Transitive KleeneEq
kleene-trans {z = e''} (kleeneq n val e-eval e'-eval) (kleeneq n' val' e'-eval2  e''-eval)
   with eval-deterministic e'-eval e'-eval2 val val'
... | eq = kleeneq _ val e-eval (ID.coe1 (λ x → e'' ~>* x) (symm eq) e''-eval)

kleene-converse-evaluation : ∀{e e' d : TNat} →
                             e ≃ e' → d ~>* e → d ≃ e'
kleene-converse-evaluation (kleeneq n val S1 S2) eval =
  kleeneq n val (eval-trans eval S1) S2
