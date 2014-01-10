module Eq.Defs where

open import Prelude
open import T
open import Contexts
import SubstTheory

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

ObservEq : TRel
ObservEq Γ A e e' = ∀(C : PCtx Γ A) → C < e > ≃ C < e' >

syntax ObservEq Γ A e e' = Γ ⊢ e ≅ e' :: A

---- Logical equivalence
LogicalEq : (A : TTp) → TCExp A → TCExp A → Set
LogicalEq nat e e' = e ≃ e'
LogicalEq (A ⇒ B) e e' = (e₁ e₁' : TCExp A) →
                         LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')

syntax LogicalEq A e e' = e ~ e' :: A


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
... | xeq = ID.coe2 (LogicalEq _)
            (SubstTheory.extend-nofail-s γ e n) (SubstTheory.extend-nofail-s γ' e' n) xeq

---- Open logical equivalence
OLogicalEq : TRel
OLogicalEq Γ A e e' = ∀{γ γ' : TSubst Γ []} → LogicalEqΓ Γ γ γ' →
                      (ssubst γ e) ~ (ssubst γ' e') :: A

syntax OLogicalEq Γ A e e' = Γ ⊢ e ~ e' :: A
