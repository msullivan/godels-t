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
  ... | keq with ID.coe1 (λ x → KleeneEq x ((C' << C >>) < e' >)) (composing-commutes C' C e) keq
  ... | keq' = ID.coe1 (KleeneEq (C' < C < e > >)) (composing-commutes C' C e') keq'

  obs-consistent : Consistent ObservEq
  obs-consistent oeq = oeq ∘

  obs-is-con-congruence : IsConsistentCongruence ObservEq
  obs-is-con-congruence = record { equiv = obs-is-equivalence
                                 ; cong = obs-congruence
                                 ; consistent = obs-consistent
                                 }

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
