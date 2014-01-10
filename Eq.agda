module Eq where

open import Prelude
open import T
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheory
open import Eq.ObsTheory
open import Eq.LogicalTheory


-- Now that we have shown that logical equivalence is a consistent congruence,
-- it follows that it is contained in observational equivalence.
obs-contains-logical : ∀{Γ} {A} → (OLogicalEq Γ A) ⊆ (ObservEq Γ A)
obs-contains-logical = obs-is-coarsest OLogicalEq log-is-con-congruence

open Eq.Defs public
open Eq.KleeneTheory public using (kleene-is-equivalence)
open Eq.ObsTheory public using (obs-is-coarsest ; obs-is-con-congruence)
