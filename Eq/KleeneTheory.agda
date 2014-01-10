module Eq.KleeneTheory where

open import Prelude
open import T
open import Eq.Defs
open import Eq.LogicalTheory
open import Eq.KleeneTheoryEarly public

-- Harper says that Kleene equality is "evidently reflexive",
-- but this requires/implies termination!
-- We pick it directly from the consistency and reflexivity of
-- logical equivalence.
-- We could also prove it using halting, which we could prove from
-- either our HT result or from reflexivity of logical equivalence.
-- This is a bit simpler.
kleene-refl : Reflexive KleeneEq
kleene-refl {e} = ological-consistent (ological-refl e)

-- For kicks, we'll prove halting for closed nats.
nats-halt : (n : TNat) → THalts n
nats-halt n with kleene-refl {n}
... | kleeneq _ val E1 _ = halts E1 val

kleene-is-equivalence : IsEquivalence KleeneEq
kleene-is-equivalence = record { refl_ = kleene-refl
                               ; sym_ = kleene-sym
                               ; trans_ = kleene-trans }
