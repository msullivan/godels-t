module Contexts where

open import Prelude
open import T

module Contexts where

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


  -- I hate having to prove this sort of theorem.
  composing-commutes : ∀{Γ A Γ' A' Γ'' A''} →
                       (C : TCtx Γ' A' Γ'' A'') →
                       (C' : TCtx Γ A Γ' A') →
                       (e : TExp Γ A) →
                       ((C << C' >>) < e >) ≡ C < C' < e > >
  composing-commutes ∘ C' e = Refl
  composing-commutes (e₁ e$ C) C' e = resp (_$_ e₁) (composing-commutes C C' e)
  composing-commutes (C $e e₂) C' e = resp (λ x → x $ e₂) (composing-commutes C C' e)
  composing-commutes (Λ C) C' e = resp Λ (composing-commutes C C' e)
  composing-commutes (suc C) C' e = resp suc (composing-commutes C C' e)
  composing-commutes (rec1 C e₀ es) C' e = resp (λ x → rec x e₀ es) (composing-commutes C C' e)
  composing-commutes (rec2 e' C es) C' e = resp (λ x → rec e' x es) (composing-commutes C C' e)
  composing-commutes (rec3 e' e₀ C) C' e = resp (λ x → rec e' e₀ x) (composing-commutes C C' e)


open Contexts public
