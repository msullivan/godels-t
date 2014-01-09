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


  -- Kleene equivalence
  -- I feel like doing this with numerals has not improved my life.
  t-numeral : Nat → TNat
  t-numeral Z = zero
  t-numeral (S n) = suc (t-numeral n)

  numeral-val : (n : Nat) → TVal (t-numeral n)
  numeral-val Z = val-zero
  numeral-val (S n) = val-suc (numeral-val n)

  val-numeral : ∀{e : TNat} → TVal e → Σ[ n :: Nat ] (e ≡ t-numeral n)
  val-numeral val-zero = Z , Refl
  val-numeral (val-suc v) with val-numeral v
  ... | n , eq = (S n) , (resp suc eq)


  _≃_ : (e e' : TNat) → Set
  e ≃ e' = Σ[ n :: Nat ] (e ~>* t-numeral n) × (e' ~>* t-numeral n)

  KleeneEq = _≃_

  -- Harper says that kleene equality is "evidently reflexive",
  -- but this requires termination!
  kleene-refl : Reflexive KleeneEq
  kleene-refl {e} with all-halt e
  ... | halts eval val with val-numeral val
  ... | n , eq = n , (ID.coe1 (_~>*_ e) eq eval) , ID.coe1 (_~>*_ e) eq eval

  kleene-sym : Symmetric KleeneEq
  kleene-sym (n , E1 , E2) = n , E2 , E1

  kleene-trans : Transitive KleeneEq
  kleene-trans {z = e''} (n , e-eval , e'-eval) (n' , e'-eval2 , e''-eval)
     with eval-deterministic e'-eval e'-eval2 (numeral-val n) (numeral-val n')
  ... | eq = n , (e-eval , ID.coe1 (λ x → e'' ~>* x) (symm eq) e''-eval)

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

  ---- Logical equivalence
  LogicalEq : (A : TTp) → TCExp A → TCExp A → Set
  LogicalEq nat e e' = e ≃ e'
  LogicalEq (A ⇒ B) e e' = (e₁ e₁' : TCExp A) →
                           LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')

  syntax LogicalEq A e e' = e ~ e' :: A


  logical-sym : ∀{A} → Symmetric (LogicalEq A)
  logical-sym {nat} (n , fst , snd) = n , (snd , fst)
  logical-sym {A ⇒ B} equiv = λ e₁ e₁' x → logical-sym {B}
                                            (equiv e₁' e₁ (logical-sym {A} x))

  logical-trans : ∀{A} → Transitive (LogicalEq A)
  logical-trans {nat} eq1 eq2 = kleene-trans eq1 eq2
  logical-trans {A ⇒ B} {e} {e'} {e''} eq1 eq2 =
     λ e₁ e₁' x → logical-trans (eq1 e₁ e₁ (logical-trans x (logical-sym x))) (eq2 e₁ e₁' x)
