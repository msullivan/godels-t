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


nat-val-weakening : ∀{Γ} {n : TNat} → TVal n →
                    Σ[ e :: TExp Γ nat ] (∀{γ : TSubst Γ []} → n ≡ ssubst γ e)
nat-val-weakening val-zero = zero , (λ {γ} → Refl)
nat-val-weakening {Γ} {suc n} (val-suc v) with nat-val-weakening {Γ} v
... | e , subst-thing = (suc e) , (λ {γ} → resp suc subst-thing)


-- This is sort of silly.
nat-logical-equiv-val : ∀{Γ} (γ : TSubst Γ []) (e : TExp Γ nat) →
                        Σ[ n :: TExp Γ nat ] ((ssubst γ n ~ ssubst γ e :: nat) × TVal (ssubst γ n))
nat-logical-equiv-val {Γ} γ e with kleene-refl {ssubst γ e}
... | kleeneq n val E1 E2 with nat-val-weakening {Γ} val
... | n' , is-val = n' , ((kleeneq n val (ID.coe1 (λ x → x ~>* n) is-val eval-refl) E1) ,
                          ID.coe1 TVal is-val val)

logical-contains-def : ∀{Γ} {A} → DefEq Γ A ⊆ OLogicalEq Γ A
logical-contains-def {y = e} def-refl η = ological-refl e η
logical-contains-def {x = e} {y = e'} (def-sym defeq) η =
  ological-sym {_} {_} {e'} {e} (logical-contains-def defeq) η
logical-contains-def {x = e} {y = e''} (def-trans {e' = e'} defeq1 defeq2) η
  with logical-contains-def defeq1 | logical-contains-def defeq2
... | leq1 | leq2 = ological-trans {_} {_} {e} {e'} {e''} leq1 leq2 η
logical-contains-def (def-cong defeq C) η = ological-is-congruence (logical-contains-def defeq) C η
logical-contains-def {Γ} {A} (def-beta {e = e} {e' = e'}) {γ} {γ'} η
  with step-beta {e = (ssubst (liftγ γ) e)} {e' = ssubst γ e'}
... | step with ological-refl e (extendLogicalEQΓ η (ological-refl e' η))

... | leq with subeq (compose-subst-noob γ' e') e ≡≡ subcomp γ' (singγ e') e
... | subeq-r with subcomp (singγ (ssubst γ e')) (liftγ γ) e
... | subeq-l with ID.coe2 (LogicalEq A) subeq-l subeq-r leq
... | leq' = logical-converse-evaluation-1 leq' (eval-step step)

logical-contains-def {Γ} {A} (def-rec-z {e0 = e0} {es = es}) {γ} {γ'} η with ological-refl e0 η
... | leq = logical-converse-evaluation-1 leq (eval-step step-rec-z)

-- This is super nasty. It has some code duplication when handling the congruence stuff.
-- And it also needs to deal with a bunch of nasty substitution crap.
-- The main source of nonstupid complication is that the step rule requires
-- n to be a value, and definitional equivalence does not.
logical-contains-def {Γ} {A} (def-rec-s {e = en} {e0 = e0} {es = es}) {γ} {γ'} η
  with nat-logical-equiv-val γ en
... | n , num-leq , is-val with ological-refl (rec en e0 es) η

... | full-leq with ological-is-congruence {e = ssubst γ n} {e' = ssubst γ en}
                    (closed-logical-imp-open num-leq) (rec1 ∘ (ssubst γ e0) (ssubst (liftγ γ) es))
                    (emptyLogicalEqΓ {γ = emptyγ} {γ' = emptyγ})
... | eq-with-γn-and-nasty-subst with ID.coe2 (LogicalEq A) (subid _) (subid _) eq-with-γn-and-nasty-subst
... | eq-with-γn with logical-trans eq-with-γn full-leq

... | leq-subrec with ological-refl (rec (suc en) e0 es) (logicalγ-refl {x = γ})
... | full-leq-s with ological-is-congruence {e = ssubst γ n} {e' = ssubst γ en}
                    (closed-logical-imp-open num-leq) (rec1 (suc ∘) (ssubst γ e0) (ssubst (liftγ γ) es))
                    (emptyLogicalEqΓ {γ = emptyγ} {γ' = emptyγ})
... | eq-with-sγn-and-nasty-subst with ID.coe2 (LogicalEq A) (subid _) (subid _) eq-with-sγn-and-nasty-subst
... | eq-with-sγn with logical-trans eq-with-sγn full-leq-s
... | leq-subrec-2 with ological-refl es (extendLogicalEQΓ η leq-subrec)

... | leq-unrolled with subeq (compose-subst-noob γ' (rec en e0 es)) es ≡≡
                        subcomp γ' (singγ (rec en e0 es)) es
... | subeq-l with subcomp (singγ (ssubst γ (rec n e0 es))) (liftγ γ) es
... | subeq-r with ID.coe2 (LogicalEq A) subeq-r subeq-l leq-unrolled
... | leq with step-rec-s {e = ssubst γ n} {e₀ = ssubst γ e0} {es = ssubst (liftγ γ) es} is-val
... | step with logical-converse-evaluation-1 leq (eval-step step)
... | leq-stepped = logical-trans (logical-sym leq-subrec-2) leq-stepped
