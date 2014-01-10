module Eq.Theory where

open import Prelude
open import T
open import DynTheory
open import SubstTheory
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheory
open import Eq.ObsTheory
open import Eq.LogicalTheory

-- Theory about the interactions between the relationships between the equivs

-- Now that we have shown that logical equivalence is a consistent congruence,
-- it follows that it is contained in observational equivalence.
obs-contains-logical : ∀{Γ} {A} → (OLogicalEq Γ A) ⊆ (ObservEq Γ A)
obs-contains-logical = obs-is-coarsest OLogicalEq log-is-con-congruence



--
