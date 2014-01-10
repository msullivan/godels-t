module Eq where

open import Prelude
open import T
open import SubstTheory
open import DynTheory
open import HT
open import Contexts

module Eq where

  -- General stuff about relations
  Rel : Set → Set1
  Rel A = A → A → Set

  Reflexive : ∀{A} → Rel A → Set
  Reflexive R = ∀{x} → R x x
  Symmetric : ∀{A} → Rel A → Set
  Symmetric R = ∀{x y} → R x y → R y x
  Transitive : ∀{A} → Rel A → Set
  Transitive R = ∀{x y z} → R x y → R y z → R x z

  _⊆_ : ∀{A} → Rel A → Rel A → Set
  P ⊆ Q = ∀{x y} → P x y → Q x y
  Includes = _⊆_

  record IsEquivalence {A : Set}
                       (R : Rel A) : Set  where
    field
      refl_  : Reflexive R
      sym_   : Symmetric R
      trans_ : Transitive R

  TRel = (Γ : Ctx) (A : TTp) → Rel (TExp Γ A)

  -- Specific relation stuff about T
  Congruence : TRel → Set
  Congruence R = ∀{Γ} {A} {e e' : TExp Γ A} →
                 R Γ A e e' →
                 {Γ' : Ctx} {A' : TTp} → (C : TCtx Γ A Γ' A') →
                 R Γ' A' (C < e >) (C < e' >)

  -- Kleene equivalence
  record KleeneEq (e e' : TNat) : Set where
    constructor kleeneq
    field
      n : TNat
      val : TVal n
      S1 : e ~>* n
      S2 : e' ~>* n

  _≃_ = KleeneEq

  -- Definition of consistency
  Consistent : TRel → Set
  Consistent R = ∀ {e e' : TNat} → R [] nat e e' → e ≃ e'

  record IsConsistentCongruence (R : TRel) : Set where
    field
      equiv : ∀{Γ A} → IsEquivalence (R Γ A)
      cong : Congruence R
      consistent : Consistent R


  -- Theory about Kleene equality

  -- Harper says that Kleene equality is "evidently reflexive",
  -- but this requires termination!
  kleene-refl : Reflexive KleeneEq
  kleene-refl {e} with all-halt e
  ... | halts eval val = kleeneq _ val eval eval

  kleene-sym : Symmetric KleeneEq
  kleene-sym (kleeneq n val S1 S2) = kleeneq n val S2 S1

  kleene-trans : Transitive KleeneEq
  kleene-trans {z = e''} (kleeneq n val e-eval e'-eval) (kleeneq n' val' e'-eval2  e''-eval)
     with eval-deterministic e'-eval e'-eval2 val val'
  ... | eq = kleeneq _ val e-eval (ID.coe1 (λ x → e'' ~>* x) (symm eq) e''-eval)
  kleene-is-equivalence : IsEquivalence KleeneEq
  kleene-is-equivalence = record { refl_ = kleene-refl
                                 ; sym_ = kleene-sym
                                 ; trans_ = kleene-trans }

  kleene-converse-evaluation : ∀{e e' d : TNat} →
                               e ≃ e' → d ~>* e → d ≃ e'
  kleene-converse-evaluation (kleeneq n val S1 S2) eval =
    kleeneq n val (eval-trans eval S1) S2

  -- Observational equivalence

  PCtx : (Γ : Ctx) (A : TTp) → Set
  PCtx Γ A = TCtx Γ A [] nat

  ObservEq : TRel
  ObservEq Γ A e e' = ∀(C : PCtx Γ A) → C < e > ≃ C < e' >

  syntax ObservEq Γ A e e' = Γ ⊢ e ≅ e' :: A

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


  ---- Logical equivalence
  LogicalEq : (A : TTp) → TCExp A → TCExp A → Set
  LogicalEq nat e e' = e ≃ e'
  LogicalEq (A ⇒ B) e e' = (e₁ e₁' : TCExp A) →
                           LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')

  syntax LogicalEq A e e' = e ~ e' :: A


  logical-sym : ∀{A} → Symmetric (LogicalEq A)
  logical-sym {nat} eq = kleene-sym eq
  logical-sym {A ⇒ B} equiv = λ e₁ e₁' x → logical-sym {B}
                                            (equiv e₁' e₁ (logical-sym {A} x))

  logical-trans : ∀{A} → Transitive (LogicalEq A)
  logical-trans {nat} eq1 eq2 = kleene-trans eq1 eq2
  logical-trans {A ⇒ B} {e} {e'} {e''} eq1 eq2 =
     λ e₁ e₁' x → logical-trans (eq1 e₁ e₁ (logical-trans x (logical-sym x))) (eq2 e₁ e₁' x)


  -- Start towards open logical equiv

  -- extend equiv to substitutions
  LogicalEqΓ : (Γ : Ctx) → TSubst Γ [] → TSubst Γ [] → Set
  LogicalEqΓ Γ γ γ' = ∀{A} (x : A ∈ Γ) → (γ x ~ γ' x :: A)

  emptyLogicalEqΓ : ∀{γ γ' : TSubst [] []} -> LogicalEqΓ [] γ γ'
  emptyLogicalEqΓ ()

  extendLogicalEQΓ : ∀{Γ A} {e e' : TCExp A} {γ γ' : TSubst Γ []} →
                     LogicalEqΓ Γ γ γ' → e ~ e' :: A →
                     LogicalEqΓ (A :: Γ) (extendγ γ e) (extendγ γ' e')
  extendLogicalEQΓ η eq Z = eq
  extendLogicalEQΓ {_} {_} {e} {e'} {γ} {γ'} η eq (S n) with η n
  ... | xeq = ID.coe2 (LogicalEq _) (extend-nofail-s γ e n) (extend-nofail-s γ' e' n) xeq

  logicalγ-sym : ∀{Γ} → Symmetric (LogicalEqΓ Γ)
  logicalγ-sym η n = logical-sym (η n)
  logicalγ-trans : ∀{Γ} → Transitive (LogicalEqΓ Γ)
  logicalγ-trans η η' n = logical-trans (η n) (η' n)

  ---- Open logical equivalence
  OLogicalEq : TRel
  OLogicalEq Γ A e e' = ∀{γ γ' : TSubst Γ []} → LogicalEqΓ Γ γ γ' →
                        (ssubst γ e) ~ (ssubst γ' e') :: A

  syntax OLogicalEq Γ A e e' = Γ ⊢ e ~ e' :: A

  ological-sym : ∀{Γ} {A} → Symmetric (OLogicalEq Γ A)
  ological-sym eq η = logical-sym (eq (logicalγ-sym η))

  -- This uses the trick where, despite not having reflexivity yet,
  -- we show that some element x is reflexive by using symmetry and
  -- transitivity on a proof of x ~ y that we have.
  -- I find this trick hilarious.
  ological-trans : ∀{Γ} {A} → Transitive (OLogicalEq Γ A)
  ological-trans eq eq' η = logical-trans (eq η)
                            (eq' (logicalγ-trans (logicalγ-sym η) η))


  logical-converse-evaluation-1 : ∀{A} {e e' d : TCExp A} →
                                  e ~ e' :: A →
                                  d ~>* e →
                                  d ~ e' :: A
  logical-converse-evaluation-1 {nat} eq eval = kleene-converse-evaluation eq eval
  logical-converse-evaluation-1 {A ⇒ B} eq eval =
    λ e₁ e₁' x → logical-converse-evaluation-1 (eq e₁ e₁' x)
                 (eval-compat step-app-l eval)

  logical-converse-evaluation : ∀{A} {e e' d d' : TCExp A} →
                                e ~ e' :: A →
                                d ~>* e →
                                d' ~>* e' →
                                d ~ d' :: A
  logical-converse-evaluation eq eval1 eval2 with logical-converse-evaluation-1 eq eval1
  ... | eq1 with logical-converse-evaluation-1 (logical-sym eq1) eval2
  ... | eq2 = logical-sym eq2

  -- This is the hard one.
  ological-refl : ∀{Γ} {A} → (e : TExp Γ A) → Γ ⊢ e ~ e :: A
  ological-refl (var x) η = η x
  ological-refl {Γ} {A ⇒ B} (Λ e) {γ = γ} {γ' = γ'} η = lam-case
    where lam-case : (e₁ e₁' : TExp [] A) → LogicalEq A e₁ e₁' →
                      LogicalEq B (Λ (ssubst (liftγ γ) e) $ e₁) (Λ (ssubst (liftγ γ') e) $ e₁')
          lam-case e₁ e₁' arg-eq with ological-refl e (extendLogicalEQΓ η arg-eq)
          ... | equiv with combine-subst-noob γ e e₁ | combine-subst-noob γ' e e₁'
          ... | eq1 | eq2 with ID.coe2 (LogicalEq B) eq1 eq2 equiv
          ... | equiv' = logical-converse-evaluation equiv'
                         (eval-step step-beta) (eval-step step-beta)
  ological-refl (e $ e') η with ological-refl e η | ological-refl e' η
  ... | eq-e | eq-e' = eq-e _ _ eq-e'
  ological-refl zero η = kleeneq zero val-zero eval-refl eval-refl
  ological-refl (suc e) η with ological-refl e η
  ... | kleeneq n val S1 S2 = kleeneq (suc n) (val-suc val)
                              (eval-compat step-suc S1) (eval-compat step-suc S2)
  ological-refl {Γ} {A} (rec e e0 es) {γ = γ} {γ' = γ'} η with ological-refl e η
  ... | kleeneq n val E1 E2 = logical-converse-evaluation (inner val)
                              (eval-compat step-rec E1) (eval-compat step-rec E2)
    where inner : {n : TNat} (val : TVal n) →
                  ((rec n (ssubst γ e0) (ssubst (liftγ γ) es)) ~
                   (rec n (ssubst γ' e0) (ssubst (liftγ γ') es)) :: A)
          inner val-zero = logical-converse-evaluation (ological-refl e0 η)
                           (eval-step step-rec-z) (eval-step step-rec-z)
          inner (val-suc val) with ological-refl es (extendLogicalEQΓ η (inner val))
          ... | equiv with combine-subst-noob γ es _ | combine-subst-noob γ' es _
          ... | eq1 | eq2 with ID.coe2 (LogicalEq A) eq1 eq2 equiv
          ... | equiv' = logical-converse-evaluation equiv'
                         (eval-step (step-rec-s val)) (eval-step (step-rec-s val))


  ological-refl' : ∀{Γ} {A} → Reflexive (OLogicalEq Γ A)
  ological-refl' {x = x} = ological-refl x

  -- I do not understand why these need to be eta expanded
  ological-is-equivalence : ∀{Γ : Ctx} {A : TTp} → IsEquivalence (OLogicalEq Γ A)
  ological-is-equivalence = record { refl_ = λ {e} → ological-refl' {_} {_} {e}
                                   ; sym_ = λ {e e'} → ological-sym {_} {_} {e} {e'}
                                   ; trans_ = λ {e e' e''} → ological-trans {_} {_} {e} {e'} {e''}}
