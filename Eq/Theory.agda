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
obs-contains-logical : ∀{Γ} {A} → OLogicalEq Γ A ⊆ ObservEq Γ A
obs-contains-logical = obs-is-coarsest OLogicalEq log-is-con-congruence

closed-logical-imp-open : ∀{A} → LogicalEq A ⊆ OLogicalEq [] A
closed-logical-imp-open {A} {e} {e'} leq {γ} {γ'} η =
  ID.coe2 (LogicalEq A) (symm (closed-subst γ e)) (symm (closed-subst γ' e')) leq

obs-contains-clogical : ∀{A} → (LogicalEq A) ⊆ (ObservEq [] A)
obs-contains-clogical leq = obs-contains-logical (closed-logical-imp-open leq)


obs-implies-closed-logical : ∀{A} {e e' : TCExp A} →
                             [] ⊢ e ≅ e' :: A →
                             e ~ e' :: A
obs-implies-closed-logical {nat} oeq = ObservEq.observe oeq ∘
obs-implies-closed-logical {A ⇒ B} {e} {e'} oeq = body
  where body : (e₁ e₁' : TExp [] A) → LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')
        body e₁ e₁' leq with obs-contains-clogical leq
        ... | oeq' with obs-trans (obs-congruence oeq' (e e$ ∘)) (obs-congruence oeq (∘ $e e₁'))
        ... | oeq'' = obs-implies-closed-logical oeq''

obs-contains-logical-subst : ∀{Γ} → SubstRel LogicalEq Γ ⊆ SubstRel (ObservEq []) Γ
obs-contains-logical-subst η x = obs-contains-clogical (η x)

logical-contains-obs : ∀{Γ} {A} → ObservEq Γ A ⊆ OLogicalEq Γ A
logical-contains-obs {Γ} {A} {e} {e'} oeq {γ} {γ'} η
  with substs-respect-obs oeq (obs-contains-logical-subst η)
... | coeq = obs-implies-closed-logical coeq
