module Eq.LogicalTheory where

open import Prelude
open import T
open import DynTheory
open import SubstTheory
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheoryEarly

-- Theory about logical equivalence

logical-sym : ∀{A} → Symmetric (LogicalEq A)
logical-sym {nat} eq = kleene-sym eq
logical-sym {A ⇒ B} equiv = λ e₁ e₁' x → logical-sym {B}
                                          (equiv e₁' e₁ (logical-sym {A} x))

logical-trans : ∀{A} → Transitive (LogicalEq A)
logical-trans {nat} eq1 eq2 = kleene-trans eq1 eq2
logical-trans {A ⇒ B} {e} {e'} {e''} eq1 eq2 =
   λ e₁ e₁' x → logical-trans (eq1 e₁ e₁ (logical-trans x (logical-sym x))) (eq2 e₁ e₁' x)


logicalγ-sym : ∀{Γ} → Symmetric (LogicalEqΓ Γ)
logicalγ-sym η n = logical-sym (η n)
logicalγ-trans : ∀{Γ} → Transitive (LogicalEqΓ Γ)
logicalγ-trans η η' n = logical-trans (η n) (η' n)


-- Open logical theory
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

-- This is basically the same proof as reflexivity...?
-- That's weird.
ological-is-congruence : Congruence OLogicalEq
ological-is-congruence leq ∘ η = leq η
ological-is-congruence leq (e₁ e$ C) η with ological-is-congruence leq C η | ological-refl e₁ η
... | equiv-rhs | equiv-lhs = equiv-lhs _ _ equiv-rhs
ological-is-congruence leq (C $e e₂) η with ological-is-congruence leq C η | ological-refl e₂ η
... | equiv-lhs | equiv-rhs = equiv-lhs _ _ equiv-rhs
ological-is-congruence {e = e} {e' = e'} leq (Λ C) {γ = γ} {γ' = γ'} η = body
  where -- I feel like I shouldn't have to give so much type information here.
        body : (e₁ e₁' : TExp [] _) →
                LogicalEq _ e₁ e₁' →
                LogicalEq _ (Λ (ssubst (liftγ _) (C < e >)) $ e₁)
               (Λ (ssubst (liftγ _) (C < e' >)) $ e₁')
        body e₁ e₁' arg-eq with ological-is-congruence {e = e} {e' = e'} leq C (extendLogicalEQΓ η arg-eq)
        ... | equiv with combine-subst-noob γ (C < e >) e₁ | combine-subst-noob γ' (C < e' >) e₁'
        ... | eq1 | eq2 with ID.coe2 (LogicalEq _) eq1 eq2 equiv
        ... | equiv' = logical-converse-evaluation equiv'
                       (eval-step step-beta) (eval-step step-beta)
ological-is-congruence leq (suc C) η with ological-is-congruence leq C η
... | kleeneq n val S1 S2 = kleeneq (suc n) (val-suc val)
                            (eval-compat step-suc S1) (eval-compat step-suc S2)
-- Is there a way to abstract out all the shit in these three bits?
ological-is-congruence {e = e} {e' = e'} leq {A' = A'} (rec1 C e0 es) {γ = γ} {γ' = γ'} η
  with ological-is-congruence leq C η
... | kleeneq n val E1 E2 = logical-converse-evaluation (inner val)
                            (eval-compat step-rec E1) (eval-compat step-rec E2)
  where inner : {n : TNat} (val : TVal n) →
                ((rec n (ssubst γ e0) (ssubst (liftγ γ) es)) ~
                 (rec n (ssubst γ' e0) (ssubst (liftγ γ') es)) :: A')
        inner val-zero = logical-converse-evaluation (ological-refl e0 η)
                         (eval-step step-rec-z) (eval-step step-rec-z)
        inner (val-suc val) with ological-refl es (extendLogicalEQΓ η (inner val))
        ... | equiv with combine-subst-noob γ es _ | combine-subst-noob γ' es _
        ... | eq1 | eq2 with ID.coe2 (LogicalEq A') eq1 eq2 equiv
        ... | equiv' = logical-converse-evaluation equiv'
                       (eval-step (step-rec-s val)) (eval-step (step-rec-s val))

ological-is-congruence {e = e} {e' = e'} leq {A' = A'} (rec2 en C es) {γ = γ} {γ' = γ'} η
  with ological-refl en η
... | kleeneq n val E1 E2 = logical-converse-evaluation (inner val)
                            (eval-compat step-rec E1) (eval-compat step-rec E2)
  where inner : {n : TNat} (val : TVal n) →
                ((rec n (ssubst γ (C < e >)) (ssubst (liftγ γ) es)) ~
                 (rec n (ssubst γ' (C < e' >)) (ssubst (liftγ γ') es)) :: A')
        inner val-zero = logical-converse-evaluation (ological-is-congruence leq C η)
                         (eval-step step-rec-z) (eval-step step-rec-z)
        inner (val-suc val) with ological-refl es (extendLogicalEQΓ η (inner val))
        ... | equiv with combine-subst-noob γ es _ | combine-subst-noob γ' es _
        ... | eq1 | eq2 with ID.coe2 (LogicalEq A') eq1 eq2 equiv
        ... | equiv' = logical-converse-evaluation equiv'
                       (eval-step (step-rec-s val)) (eval-step (step-rec-s val))

ological-is-congruence {e = e} {e' = e'} leq {A' = A'} (rec3 en e0 C) {γ = γ} {γ' = γ'} η
  with ological-refl en η
... | kleeneq n val E1 E2 = logical-converse-evaluation (inner val)
                            (eval-compat step-rec E1) (eval-compat step-rec E2)
  where inner : {n : TNat} (val : TVal n) →
                ((rec n (ssubst γ e0) (ssubst (liftγ γ) (C < e >))) ~
                 (rec n (ssubst γ' e0) (ssubst (liftγ γ') (C < e' >))) :: A')
        inner val-zero = logical-converse-evaluation (ological-refl e0 η)
                         (eval-step step-rec-z) (eval-step step-rec-z)
        inner (val-suc val) with ological-is-congruence leq C (extendLogicalEQΓ η (inner val))
        ... | equiv with combine-subst-noob γ (C < e >) _ | combine-subst-noob γ' (C < e' >) _
        ... | eq1 | eq2 with ID.coe2 (LogicalEq A') eq1 eq2 equiv
        ... | equiv' = logical-converse-evaluation equiv'
                       (eval-step (step-rec-s val)) (eval-step (step-rec-s val))

ological-consistent : Consistent OLogicalEq
ological-consistent leq with leq (emptyLogicalEqΓ {γ = emptyγ} {γ' = emptyγ})
... | keq = ID.coe2 KleeneEq (subid _) (subid _) keq


log-is-con-congruence : IsConsistentCongruence OLogicalEq
log-is-con-congruence = record { equiv = ological-is-equivalence
                               ; cong = ological-is-congruence
                               ; consistent = ological-consistent
                               }
