module Eq.ObsTheory where

open import Prelude
open import T
open import DynTheory
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheory


---- Proofs about observational equivalence

-- observational equivalence being an equiv reln follows trivially from kleene equiv being one
obs-refl : ∀ {Γ} {A} → Reflexive (ObservEq Γ A)
obs-refl C = kleene-refl
obs-sym : ∀ {Γ} {A} → Symmetric (ObservEq Γ A)
obs-sym eq C = kleene-sym (eq C)
obs-trans : ∀ {Γ} {A} → Transitive (ObservEq Γ A)
obs-trans eq1 eq2 C = kleene-trans (eq1 C) (eq2 C)

obs-is-equivalence : ∀{Γ} {A} → IsEquivalence (ObservEq Γ A)
obs-is-equivalence = record { refl_ = obs-refl
                            ; sym_ = obs-sym
                            ; trans_ = obs-trans }

obs-congruence : Congruence ObservEq
obs-congruence {e = e} {e' = e'} oeq C C' with oeq (C' << C >>)
... | keq = ID.coe2 KleeneEq (composing-commutes C' C e) (composing-commutes C' C e') keq

obs-consistent : Consistent ObservEq
obs-consistent oeq = oeq ∘

obs-is-con-congruence : IsConsistentCongruence ObservEq
obs-is-con-congruence = record { equiv = obs-is-equivalence
                               ; cong = obs-congruence
                               ; consistent = obs-consistent
                               }

-- Prove that observational equivalence is the coarsest consistent congruence.
-- That is, that it contains all other consistent congruences.
-- That is, if two terms are related by a consistent congruence, they are
-- observationally equivalence.
obs-is-coarsest : (R : TRel) → IsConsistentCongruence R →
                  {Γ : Ctx} {A : TTp} →
                  (R Γ A) ⊆ (ObservEq Γ A)
obs-is-coarsest R isCC eq C with (IsConsistentCongruence.cong isCC) eq C
... | eqC = (IsConsistentCongruence.consistent isCC) eqC
