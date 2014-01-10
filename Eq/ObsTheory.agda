module Eq.ObsTheory where

open import Prelude
open import T
open import DynTheory
import SubstTheory
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheory

open ObservEq
---- Proofs about observational equivalence

-- observational equivalence being an equiv reln follows trivially from kleene equiv being one
obs-refl : ∀ {Γ} {A} → Reflexive (ObservEq Γ A)
obs-refl = obs (λ C → kleene-refl)
obs-sym : ∀ {Γ} {A} → Symmetric (ObservEq Γ A)
obs-sym eq = obs (λ C → kleene-sym (observe eq C))
obs-trans : ∀ {Γ} {A} → Transitive (ObservEq Γ A)
obs-trans eq1 eq2 = obs (λ C → kleene-trans (observe eq1 C) (observe eq2 C))

obs-is-equivalence : ∀{Γ} {A} → IsEquivalence (ObservEq Γ A)
obs-is-equivalence = record { refl_ = obs-refl
                            ; sym_ = obs-sym
                            ; trans_ = obs-trans }

obs-congruence : Congruence ObservEq
obs-congruence {e = e} {e' = e'} oeq C = obs help
  where help : (C₁ : TCtx _ _ _ _) → KleeneEq (C₁ < C < e > >) (C₁ < C < e' > >)
        help C' with observe oeq (C' << C >>)
        ... | keq = ID.coe2 KleeneEq (composing-commutes C' C e) (composing-commutes C' C e') keq

obs-consistent : Consistent ObservEq
obs-consistent oeq = observe oeq ∘

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
obs-is-coarsest R isCC eq = obs help
  where help : (C : TCtx _ _ _ _) → KleeneEq (C < _ >) (C < _ >)
        help C with (IsConsistentCongruence.cong isCC) eq C
        ... | eqC = (IsConsistentCongruence.consistent isCC) eqC

---- Ugh.
postulate
  substs-respect-obs : ∀{Γ} {A} {e e' : TExp Γ A} {γ γ' : TSubst Γ []} →
                       Γ ⊢ e ≅ e' :: A →
                       SubstRel (ObservEq []) Γ γ γ' →
                       [] ⊢ ssubst γ e ≅ ssubst γ' e' :: A
