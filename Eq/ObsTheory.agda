module Eq.ObsTheory where

open import Prelude
open import T
open import DynTheory
open import SubstTheory
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


-- Produce a program context that is "equivalent" to a substitution.
-- Essentially the idea is, if we have a substitution
-- γ = e1/x1,...,en/xn, we produce the term
-- (λx1. ⋯ λxn. ∘) e1 ⋯ en
--
-- It took me a while of fiddling around before I came up with this
-- implementation based on composing contexts, but it works really nicely.
--
-- The earlier version that I got closest to making work placed the
-- terms we were substituting underneath other lambdas, which almost
-- works; since it requires weakening the terms, it means to prove
-- subst-ctx-respect-obs we would need to show that weakening preserves
-- observational equivalence. I don't know how to do this without using
-- that observational and logical equivalence coincide.
subst-ctx : ∀{Γ C} → (γ : TSubst Γ []) → (TCtx Γ C [] C)
subst-ctx {[]} γ = ∘
subst-ctx {A :: Γ} {C} γ with (subst-ctx {Γ} {A ⇒ C} (dropγ γ))
... | D = (D << Λ ∘ >>) $e (γ Z)

-- This would basically be the end of the world in call by value.
-- On paper, this proof goes:
--
-- Given some substitution γ[x -> e'], want to show that
-- (C << (λ x. ∘) >> e') < e > e'~>* γ[x -> e'](e), where C is the context constructed for γ.
-- We know that (C << (λ x. ∘) >> e') < e > = C << (λ x. e) >> e'.
-- By induction, we have that "C << (λ x. e) >> ~>* (λ x. γ(e))", and by compatability rules,
-- C << (λ x. e) >> e' ~>* (λ x. γ(e)) e'
-- Then, by beta, we have that (λ x. γ(e)) e' ~> γ([e'/x]e)).
subst-ctx-substs : ∀{Γ A} → (γ : TSubst Γ []) → (e : TExp Γ A) →
                   (subst-ctx γ) < e > ~>* ssubst γ e
subst-ctx-substs {[]} γ e = ID.coe1 (_~>*_ e) (symm (closed-subst γ e)) eval-refl
subst-ctx-substs {x :: Γ} γ e with subst-ctx-substs (dropγ γ) (Λ e)
... | recursive-eval with eval-compat (step-app-l {e₂ = γ Z}) recursive-eval
... | compat-eval with step-beta {e = ssubst (liftγ (dropγ γ)) e} {e' = γ Z}
... | step with eval-trans compat-eval (eval-step step)

... | eval with composing-commutes (subst-ctx (dropγ γ)) (Λ ∘) e
... | ctx-eq with (symm (subcomp (singγ (γ Z)) (liftγ (dropγ γ)) e) ≡≡ symm (subeq (drop-fix γ) e))
... | subst-eq = ID.coe2 (λ y z → (y $ γ Z) ~>* z) (symm ctx-eq) subst-eq eval

-- Straightforward extension of the above theorem to kleene equivalence at nat type.
subst-ctx-substs-eq : ∀{Γ} → (γ : TSubst Γ []) → (e : TExp Γ nat) →
                     (subst-ctx γ) < e > ≃ ssubst γ e
subst-ctx-substs-eq γ e with subst-ctx-substs γ e | kleene-refl {x = ssubst γ e}
... | eval | kleeneq n val E1 E2 = kleeneq n val (eval-trans eval E1) E2

-- Prove that observationally equivalent substitutions yield
-- contexts that are observationally equivalent when applied to a term.
subst-ctx-respect-obs : ∀{Γ} {A} (e : TExp Γ A) {γ γ' : TSubst Γ []} →
                         SubstRel (ObservEq []) Γ γ γ' →
                         [] ⊢ subst-ctx γ < e > ≅ subst-ctx γ' < e > :: A
subst-ctx-respect-obs {[]} e η = obs-refl
subst-ctx-respect-obs {B :: Γ} {A} e {γ} {γ'} η with
  subst-ctx-respect-obs (Λ e) {dropγ γ} {dropγ γ'} (λ x → η (S x))
... | D-D'-equiv with obs-congruence D-D'-equiv (∘ $e γ Z)
... | cong1 with obs-congruence (η Z) ((subst-ctx (dropγ γ') < Λ e >) e$ ∘)
... | cong2 with obs-trans cong1 cong2
... | equiv =
  ID.coe2 (ObservEq [] A)
  (symm (resp (λ x → x $ γ Z) (composing-commutes (subst-ctx (dropγ γ)) (Λ ∘) e)))
  (symm (resp (λ x → x $ γ' Z) (composing-commutes (subst-ctx (dropγ γ')) (Λ ∘) e)))
  equiv

-- Applying a substitution to two obs equivalent terms yields observational equivalent output.
-- Takes advantage of substitution contexts.
substs-respect-obs-1 : ∀{Γ} {A} {e e' : TExp Γ A} {γ : TSubst Γ []} →
                       Γ ⊢ e ≅ e' :: A →
                       [] ⊢ ssubst γ e ≅ ssubst γ e' :: A
substs-respect-obs-1 {Γ} {A} {e} {e'} {γ} (obs observe) = obs help
  where help : (C : TCtx [] A [] nat) → KleeneEq (C < ssubst γ e >) (C < ssubst γ e' >)
        help C with observe (subst-ctx γ << weaken-closed-tctx C >>)
        ... | D-equiv with ID.coe2 KleeneEq
                           (composing-commutes (subst-ctx γ) (weaken-closed-tctx C) e)
                           (composing-commutes (subst-ctx γ) (weaken-closed-tctx C) e')
                           D-equiv
        ... | D-equiv2 with subst-ctx-substs-eq γ ((weaken-closed-tctx C) < e >) |
                            subst-ctx-substs-eq γ ((weaken-closed-tctx C) < e' >)
        ... | sub-equiv1 | sub-equiv2 with
          kleene-trans (kleene-sym sub-equiv1) (kleene-trans D-equiv2 sub-equiv2)
        ... | equiv = ID.coe2 KleeneEq
              (symm (subst-commutes-w-closed-tctx γ C e))
                (symm (subst-commutes-w-closed-tctx γ C e')) equiv

-- Applying observationally equivalent substitutions a term
-- yields observational equivalent output.
-- Takes advantage of substitution contexts.
-- There is much in this proof that is similar to substs-respect-obs-1.
-- Maybe they could have been merged more?
substs-respect-obs-2 : ∀{Γ} {A} (e : TExp Γ A) {γ γ' : TSubst Γ []} →
                       SubstRel (ObservEq []) Γ γ γ' →
                       [] ⊢ ssubst γ e ≅ ssubst γ' e :: A
substs-respect-obs-2 {Γ} {A} e {γ} {γ'} η = obs help
  where help : (C : TCtx [] A [] nat) → KleeneEq (C < ssubst γ e >) (C < ssubst γ' e >)
        help C with subst-ctx-respect-obs (weaken-closed-tctx C < e >) η
        ... | oeq with obs-consistent oeq
        ... | keq with subst-ctx-substs-eq γ ((weaken-closed-tctx C) < e >) |
                       subst-ctx-substs-eq γ' ((weaken-closed-tctx C) < e >)
        ... | sub-equiv1 | sub-equiv2 with
          kleene-trans (kleene-sym sub-equiv1) (kleene-trans keq sub-equiv2)
        ... | equiv = ID.coe2 KleeneEq
              (symm (subst-commutes-w-closed-tctx γ C e))
              (symm (subst-commutes-w-closed-tctx γ' C e)) equiv

-- Combine the two previous theorems.
substs-respect-obs : ∀{Γ} {A} {e e' : TExp Γ A} {γ γ' : TSubst Γ []} →
                     Γ ⊢ e ≅ e' :: A →
                     SubstRel (ObservEq []) Γ γ γ' →
                     [] ⊢ ssubst γ e ≅ ssubst γ' e' :: A
substs-respect-obs {Γ} {A} {e} {e'} {γ} {γ'} oeq η =
  obs-trans (substs-respect-obs-2 e η) (substs-respect-obs-1 oeq)
