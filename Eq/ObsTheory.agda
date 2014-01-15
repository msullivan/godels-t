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
--
-- We do this differently than Bob does in his book.
-- Bob builds one big lambda and then does all the applications.
-- That is nice, because no weakening needs to happen, but also
-- requires multiple inductions.
-- It took me a while of fiddling around before I came up with this
-- formulation based on composing contexts, but it works really nicely.
--
-- I had some previous versions that produced the right term but for which
-- there didn't seem to be a good way to prove subst-ctx-substs.
-- (Essentially it was tail-recursively doing the substitution composition internally.)
subst-ctx : ∀{Γ C} → (γ : TSubst Γ []) → (TCtx Γ C [] C)
subst-ctx {[]} γ = ∘
subst-ctx {A :: Γ} γ with (Λ ∘ $e weaken-closed (γ Z))
... | app = (subst-ctx (dropγ γ)) << app >>

-- This would basically be the end of the world in call by value.
-- Most of the nastiness here is in coercing things up to equality
-- on substitutions and contexts that compose.
-- On paper, the main bit would be pretty simple:
--
-- Given some substitution γ[x -> e'], want to show that
-- C << (λ x. ∘) e' >> < e > ~>* γ[x -> e'](e), where C is the context constructed for γ.
-- We know that C << (λ x. ∘) e' >> < e > = C << (λ x. e) e' >>.
-- By induction, we have that "C << (λ x. e) e' >> ~>* (λ x. γ(e)) e'" (we know that e' is closed).
-- Then, by beta, we have that (λ x. γ(e)) e' ~> γ([e'/x]e)).
--
-- Of course, everything gets nastier here, but that is the key idea. I wonder if there is
-- a way to reduce the massive nastiness of all the coe1s.
--
-- Originally I tried to formulate this as proving the terms were Kleene equivalent
-- (the output type was restricted to nat), but this turns out to not be strong enough.
-- (It would require definitional equivalence to be contained in observational equivalence,
-- and our proof of that depends on this.)
subst-ctx-substs : ∀{Γ A} → (γ : TSubst Γ []) → (e : TExp Γ A) →
                   (subst-ctx γ) < e > ~>* ssubst γ e
subst-ctx-substs {[]} γ e = ID.coe1 (_~>*_ e) (symm (closed-subst γ e)) eval-refl
subst-ctx-substs {B :: Γ} γ e with composing-commutes (subst-ctx (λ {A} n → γ (S n)))
                                                      (Λ ∘ $e ren closed-wkγ (γ Z))
                                                      e
... | ctx-eq with subst-ctx-substs (dropγ γ) (Λ e $ ren closed-wkγ (γ Z))

... | recursive-case with
  ID.coe1 (λ z → (subst-ctx (λ {A} n → γ (S n)) < Λ e $ ren closed-wkγ (γ Z) >)
                                   ~>* (Λ (ssubst (liftγ (λ {A} n → γ (S n))) e) $ z))
          (subren (dropγ γ) closed-wkγ (γ Z) ≡≡ closed-subst (γ o S o closed-wkγ) (γ Z))
          recursive-case

... | clean-recursive with step-beta {e = ssubst (liftγ (λ {A} n → γ (S n))) e} {e' = γ Z}
... | step with ID.coe1 (λ z → (Λ (ssubst (liftγ (dropγ γ)) e) $ γ Z) ~> z)
                (symm (subcomp (singγ (γ Z)) (liftγ (dropγ γ)) e) ≡≡ symm (subeq (drop-fix γ) e))
                step
... | step2 with eval-trans clean-recursive (eval-step step2)
... | eval = ID.coe1 (λ y → y ~>* ssubst γ e) (symm ctx-eq) eval

subst-ctx-substs-eq : ∀{Γ} → (γ : TSubst Γ []) → (e : TExp Γ nat) →
                     (subst-ctx γ) < e > ≃ ssubst γ e
subst-ctx-substs-eq γ e with subst-ctx-substs γ e | kleene-refl {x = ssubst γ e}
... | eval | kleeneq n val E1 E2 = kleeneq n val (eval-trans eval E1) E2


---- Ugh.
postulate
  substs-respect-obs : ∀{Γ} {A} {e e' : TExp Γ A} {γ γ' : TSubst Γ []} →
                       Γ ⊢ e ≅ e' :: A →
                       SubstRel (ObservEq []) Γ γ γ' →
                       [] ⊢ ssubst γ e ≅ ssubst γ' e' :: A
