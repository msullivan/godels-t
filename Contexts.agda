module Contexts where

open import Prelude
open import T
open import SubstTheory

module Contexts where

  -- Has a hole of type (Γ ⊢ A), produces a term of type (Γ' ⊢ A')
  data TCtx (Γ : Ctx) (A : TTp) : (Γ' : Ctx) → (A' : TTp) → Set where
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


  -- If the hole is closed, then the rest needs to be too.
  tctx-empty-thing : ∀{F : Set} {Γ A A' B} → TCtx [] A (B :: Γ) A' → F
  tctx-empty-thing (e₁ e$ C) = tctx-empty-thing C
  tctx-empty-thing (C $e e₂) = tctx-empty-thing C
  tctx-empty-thing (Λ C) = tctx-empty-thing C
  tctx-empty-thing (suc C) = tctx-empty-thing C
  tctx-empty-thing (rec1 C e₀ es) = tctx-empty-thing C
  tctx-empty-thing (rec2 e C es) = tctx-empty-thing C
  tctx-empty-thing (rec3 e e₀ C) = tctx-empty-thing C


  -- Very restricted function for weakening a program context where
  -- the hole also occurs under no free variables.
  weaken-closed-tctx : ∀{Γ A A'} → TCtx [] A [] A' → TCtx Γ A Γ A'
  weaken-closed-tctx ∘ = ∘
  weaken-closed-tctx (e₁ e$ C) = weaken-closed e₁ e$ weaken-closed-tctx C
  weaken-closed-tctx (C $e e₂) = weaken-closed-tctx C $e weaken-closed e₂
  weaken-closed-tctx (Λ C) = tctx-empty-thing C
  weaken-closed-tctx (suc C) = suc (weaken-closed-tctx C)
  weaken-closed-tctx (rec1 C e₀ es) =
    rec1 (weaken-closed-tctx C) (weaken-closed e₀) (ren (wk closed-wkγ) es)
  weaken-closed-tctx (rec2 e C es) =
    rec2 (weaken-closed e) (weaken-closed-tctx C) (ren (wk closed-wkγ) es)
  weaken-closed-tctx (rec3 e e₀ C) = tctx-empty-thing C

  -- Substitution commutes with a closed context
  subst-commutes-w-closed-tctx : ∀{Γ A A'} → (γ : TSubst Γ []) → (C : TCtx [] A [] A') → (e : TExp Γ A) →
                                 C < ssubst γ e > ≡ ssubst γ ((weaken-closed-tctx C) < e >)
  subst-commutes-w-closed-tctx γ ∘ e = Refl
  subst-commutes-w-closed-tctx γ (e₁ e$ C) e =
    resp2 _$_
    (symm (closed-subst _ e₁) ≡≡ symm (subren γ closed-wkγ e₁))
    (subst-commutes-w-closed-tctx γ C e)
  subst-commutes-w-closed-tctx γ (C $e e₂) e =
    resp2 _$_
    (subst-commutes-w-closed-tctx γ C e)
    (symm (closed-subst _ e₂) ≡≡ symm (subren γ closed-wkγ e₂))
  subst-commutes-w-closed-tctx γ (Λ C) e = tctx-empty-thing C
  subst-commutes-w-closed-tctx γ (suc C) e =
    resp suc (subst-commutes-w-closed-tctx γ C e)
  subst-commutes-w-closed-tctx γ (rec1 C e₀ es) e with subren (liftγ γ) (wk closed-wkγ) es
  ... | lol1 with subeq (liftwk γ closed-wkγ) es
  ... | lol2 with lift-closed-subst (γ o closed-wkγ) es
  ... | lol3 with symm lol3 ≡≡ symm lol2 ≡≡ symm lol1
  ... | lol = resp3 rec
              (subst-commutes-w-closed-tctx γ C e)
              (symm (closed-subst _ e₀) ≡≡ symm (subren γ closed-wkγ e₀))
              lol
  subst-commutes-w-closed-tctx γ (rec2 en C es) e with subren (liftγ γ) (wk closed-wkγ) es
  ... | lol1 with subeq (liftwk γ closed-wkγ) es
  ... | lol2 with lift-closed-subst (γ o closed-wkγ) es
  ... | lol3 with symm lol3 ≡≡ symm lol2 ≡≡ symm lol1
  ... | lol = resp3 rec
              (symm (closed-subst _ en) ≡≡ symm (subren γ closed-wkγ en))
              (subst-commutes-w-closed-tctx γ C e)
              lol
  subst-commutes-w-closed-tctx γ (rec3 e e₀ C) e₁ = tctx-empty-thing C


open Contexts public
