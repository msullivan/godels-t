module Eq where

open import Prelude
open import T
open import SubstTheory
open import DynTheory


module Eq where

  t-numeral : Nat → TNat
  t-numeral Z = zero
  t-numeral (S n) = suc (t-numeral n)

  numeral-val : (n : Nat) → TVal (t-numeral n)
  numeral-val Z = val-zero
  numeral-val (S n) = val-suc (numeral-val n)

  _≃_ : (e e' : TNat) → Set
  e ≃ e' = Σ[ n :: Nat ] (e ~>* t-numeral n) × (e' ~>* t-numeral n)

  KleeneEq = _≃_

  data TCtx (Γ : Ctx) (A : TTp) : Ctx → TTp → Set where
    ∘ : TCtx Γ A Γ A
    _e$_ : ∀{Γ' A' B} (e₁ : TExp Γ' (A' ⇒ B)) (C₂ : TCtx Γ A Γ' A') → TCtx Γ A Γ' B
    _$e_ : ∀{Γ' A' B} (C₁ : TCtx Γ A Γ' (A' ⇒ B)) (e₂ : TExp Γ' A') → TCtx Γ A Γ' B

    Λ : ∀{A₁ A₂ Γ'} (C : TCtx Γ A (A₁ :: Γ') A₂) → TCtx Γ A Γ' (A₁ ⇒ A₂)
    suc : ∀{Γ'} (C : TCtx Γ A Γ' nat) → TCtx Γ A Γ' nat

    rec1 : ∀{Γ' B} → (C : TCtx Γ A Γ' nat) → (e₀ : TExp Γ' B) → (es : TExp (B :: Γ') B) →
                     TCtx Γ A Γ' B
    rec2 : ∀{Γ' B} → (e : TExp Γ' nat) → (C₀ : TCtx Γ A Γ' B) → (es : TExp (B :: Γ') B) →
                     TCtx Γ A Γ' B
    rec3 : ∀{Γ' B} → (e : TExp Γ' nat) → (e₀ : TExp Γ' B) → (Cs : TCtx Γ A (B :: Γ') B) →
                     TCtx Γ A Γ' B

  _<_> : ∀{Γ A Γ' A'} → TCtx Γ A Γ' A' → TExp Γ A → TExp Γ' A'
  ∘ < e' > = e'
  (e₁ e$ C₂) < e' > = e₁ $ C₂ < e' >
  (C₁ $e e₂) < e' > = C₁ < e' > $ e₂
  Λ C < e' > = Λ (C < e' >)
  suc C < e' > = suc (C < e' >)
  rec1 C e₀ es < e' > = rec (C < e' >) e₀ es
  rec2 e C₀ es < e' > = rec e (C₀ < e' >) es
  rec3 e e₀ Cs < e' > = rec e e₀ (Cs < e' >)

  _<<_>> : ∀{Γ A Γ' A' Γ'' A''} → TCtx Γ' A' Γ'' A'' → TCtx Γ A Γ' A' →
            TCtx Γ A Γ'' A''
  ∘ << C' >> = C'
  (e₁ e$ C₂) << C' >> = e₁ e$ C₂ << C' >>
  (C₁ $e e₂) << C' >> = C₁ << C' >> $e e₂
  Λ C << C' >> = Λ (C << C' >>)
  suc C << C' >> = suc (C << C' >>)
  rec1 C e₀ es << C' >> = rec1 (C << C' >>) e₀ es
  rec2 e C₀ es << C' >> = rec2 e (C₀ << C' >>) es
  rec3 e e₀ Cs << C' >> = rec3 e e₀ (Cs << C' >>)

  TReln = (Γ : Ctx) (A : TTp) (e e' : TExp Γ A) → Set

  PCtx : (Γ : Ctx) (A : TTp) → Set
  PCtx Γ A = TCtx Γ A [] nat

  ObservEq : TReln
  ObservEq Γ A e e' = ∀(C : PCtx Γ A) → C < e > ≃ C < e' >

  syntax ObservEq Γ A e e' = Γ ⊢ e ≅ e' :: A
--  _⊢_≅_:_ (e e' : TNat) → Set

  LogicalEq : (A : TTp) → TCExp A → TCExp A → Set
  LogicalEq nat e e' = e ≃ e'
  LogicalEq (A ⇒ B) e e' = (e₁ e₁' : TCExp A) →
                           LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')

  syntax LogicalEq A e e' = e ~ e' :: A

  kleene-trans : ∀ {e e' e'' : TNat} → e ≃ e' → e' ≃ e'' → e ≃ e''
  kleene-trans {e'' = e''} (n , e-eval , e'-eval) (n' , e'-eval2 , e''-eval)
     with eval-deterministic e'-eval e'-eval2 (numeral-val n) (numeral-val n')
  ... | eq = n , (e-eval , ID.coe1 (λ x → e'' ~>* x) (symm eq) e''-eval)

  logical-symm : ∀{A} {e e' : TCExp A} → e ~ e' :: A → e' ~ e :: A
  logical-symm {nat} (n , fst , snd) = n , (snd , fst)
  logical-symm {A ⇒ B} equiv = λ e₁ e₁' x → logical-symm {B}
                                            (equiv e₁' e₁ (logical-symm {A} x))

  logical-trans : ∀{A} {e e' e'' : TCExp A} → e ~ e' :: A → e' ~ e'' :: A → e ~ e'' :: A
  logical-trans {nat} eq1 eq2 = kleene-trans eq1 eq2
  logical-trans {A ⇒ B} {e} {e'} {e''} eq1 eq2 =
     λ e₁ e₁' x → logical-trans (eq1 e₁ e₁ (logical-trans x (logical-symm x))) (eq2 e₁ e₁' x)
