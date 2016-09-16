module Eq.Defs where

open import Prelude
open import T
open import Contexts
import SubstTheory

infix 30 _⊆_ _≃_ _≃_

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
CRel = (A : TTp) → Rel (TExp [] A)

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
    E1 : e ~>* n
    E2 : e' ~>* n

_≃_ = KleeneEq

-- Definition of consistency:
-- a relation is consistent if it respects Kleene equivalence
Consistent : TRel → Set
Consistent R = ∀ {e e' : TNat} → R [] nat e e' → e ≃ e'

record IsConsistentCongruence (R : TRel) : Set where
  field
    equiv : ∀{Γ A} → IsEquivalence (R Γ A)
    cong : Congruence R
    consistent : Consistent R


-- Observational equivalence
PCtx : (Γ : Ctx) (A : TTp) → Set
PCtx Γ A = TCtx Γ A [] nat

-- This is a record in the hopes that it will be easier to read.
-- Doing it this way also has a lot of annoying drawbacks when
-- actually proving observational eqs.
record ObservEq (Γ : Ctx) (A : TTp) (e e' : TExp Γ A) : Set where
  constructor obs
  field
    observe : ∀(C : PCtx Γ A) → C < e > ≃ C < e' >

syntax ObservEq Γ A e e' = Γ ⊢ e ≅ e' :: A

---- Logical equivalence
LogicalEq : CRel
LogicalEq nat e e' = e ≃ e'
LogicalEq (A ⇒ B) e e' = (e₁ e₁' : TCExp A) →
                         LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')

syntax LogicalEq A e e' = e ~ e' :: A


-- Need a notion of pairs of closing substitutions that respect a relation on closed terms
-- Relations on closed terms

SubstRel : (R : CRel) (Γ : Ctx) → TSubst Γ [] → TSubst Γ [] → Set
SubstRel R Γ γ γ' = ∀{A} (x : A ∈ Γ) → (R A (γ x) (γ' x))

emptySubstRel : ∀(R : CRel) {γ γ' : TSubst [] []} -> SubstRel R [] γ γ'
emptySubstRel R ()

extendSubstRel : ∀(R : CRel) {Γ A} {e e' : TCExp A} {γ γ' : TSubst Γ []} →
                   SubstRel R Γ γ γ' → (R A e e') →
                   SubstRel R (A :: Γ) (extendγ γ e) (extendγ γ' e')
extendSubstRel R η eq Z = eq
extendSubstRel R {_} {_} {e} {e'} {γ} {γ'} η eq (S n) with η n
... | xeq = ID.coe2 (R _)
            (SubstTheory.extend-nofail-s γ e n) (SubstTheory.extend-nofail-s γ' e' n) xeq

-- Specialize that stuff for logical equivalence
LogicalEqΓ = SubstRel LogicalEq
emptyLogicalEqΓ = emptySubstRel LogicalEq
extendLogicalEQΓ = extendSubstRel LogicalEq

---- Open logical equivalence
OLogicalEq : TRel
OLogicalEq Γ A e e' = ∀{γ γ' : TSubst Γ []} → LogicalEqΓ Γ γ γ' →
                      (ssubst γ e) ~ (ssubst γ' e') :: A

syntax OLogicalEq Γ A e e' = Γ ⊢ e ~ e' :: A


---- Definitional (beta) equivalence
-- Definitional equivalence is the strongest congruence closed under
-- the beta axioms. Dunno what the best way to define this is,
-- so I'm just going to define it with constructors for refl/sym/trans
-- and congruence as well as the axioms.
data _==_ : ∀{Γ} {A} → TExp Γ A → TExp Γ A → Set where
  def-refl  : ∀{Γ} {A} {e : TExp Γ A} →
              e == e
  def-sym   : ∀{Γ} {A} {e e' : TExp Γ A} →
              e == e' → e' == e
  def-trans : ∀{Γ} {A} {e e' e'' : TExp Γ A} →
              e == e' → e' == e'' → e == e''

  def-cong  : ∀{Γ} {A} {e e' : TExp Γ A} →
              e == e' →
              {Γ' : Ctx} {A' : TTp} → (C : TCtx Γ A Γ' A') →
              C < e > == C < e' >

  def-beta  : ∀{Γ} {A B} {e : TExp (A :: Γ) B} {e' : TExp Γ A} →
              ((Λ e) $ e') == ssubst (singγ e') e
  def-rec-z : ∀{Γ} {A} {e0 : TExp Γ A} {es : TExp (A :: Γ) A} →
              rec zero e0 es == e0
  def-rec-s : ∀{Γ} {A} {e : TExp Γ nat} {e0 : TExp Γ A} {es : TExp (A :: Γ) A} →
              rec (suc e) e0 es == ssubst (singγ (rec e e0 es)) es

DefEq : TRel
DefEq Γ A = _==_ {Γ} {A}


---- Denotational equivalence
CDenotationalEq : CRel
CDenotationalEq A e e' = cmeaning e ≡ cmeaning e'
