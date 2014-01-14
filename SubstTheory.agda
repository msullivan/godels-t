module SubstTheory where

open import Prelude
open import T

-- I originally used postulated extensional equality to reason about
-- identical substitutions. As it turns out, it's actually somewhat
-- cleaner to appeal to a proof that using identically performing subst
-- functions produce the same outputs.

---- (Lots of theory. *Lots*. Too much. Sigh.)

module SubstTheory where

  Ren≡ : ∀ {Γ Γ'}(f g : TRen Γ Γ') → Set
  Ren≡ f g = ∀ {A} x → f {A} x ≡ g {A} x

  -- Some theorems about renamings
  wkeq : ∀{Γ Γ' A} {f g : TRen Γ Γ'} → Ren≡ f g → Ren≡ (wk {A = A} f) (wk g)
  wkeq eq Z = Refl
  wkeq eq (S n) = resp S (eq n)

  -- Prove that applying equal renamings produces equal outputs
  reneq : ∀{Γ Γ' A} {f g : TRen Γ Γ'} → Ren≡ f g → (e : TExp Γ A) → ren f e ≡ ren g e
  reneq eq (var x) = resp var (eq x)
  reneq eq (Λ e) = resp Λ (reneq (wkeq eq) e)
  reneq eq (e₁ $ e₂) = resp2 _$_ (reneq eq e₁) (reneq eq e₂)
  reneq eq zero = Refl
  reneq eq (suc e) = resp suc (reneq eq e)
  reneq eq (rec e e₀ es) = resp3 rec (reneq eq e) (reneq eq e₀) (reneq (wkeq eq) es)

  wkid : ∀{Γ A C} (x : A ∈ C :: Γ) → wk renId x ≡ renId x
  wkid Z = Refl
  wkid (S n) = Refl

  renid : ∀{Γ A} (e : TExp Γ A) → ren renId e ≡ id _ e
  renid (var x) = Refl
  renid (Λ e) = resp Λ (reneq wkid e ≡≡ renid e)
  renid (e₁ $ e₂) = resp2 _$_ (renid e₁) (renid e₂)
  renid zero = Refl
  renid (suc e) = resp suc (renid e)
  renid (rec e e₀ es) = resp3 rec (renid e) (renid e₀)
                        (reneq wkid es ≡≡ renid es)

  wkcomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {C A} (x : A ∈ (C :: B)) →
             wk (renComp f g) x ≡ (wk f o wk g) x
  wkcomp f g Z = Refl
  wkcomp f g (S n) = Refl

  rencomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {A} (e : TExp B A) →
             ren (renComp f g) e ≡ (ren f o ren g) e
  rencomp f g (var x) = Refl
  rencomp f g (Λ e) = resp Λ (reneq (wkcomp f g) e
                              ≡≡ (rencomp (wk f) (wk g) e))
  rencomp f g (e₁ $ e₂) = resp2 _$_ (rencomp f g e₁) (rencomp f g e₂)
  rencomp f g zero = Refl
  rencomp f g (suc e) = resp suc (rencomp f g e)
  rencomp f g (rec e e₀ es) = resp3 rec (rencomp f g e) (rencomp f g e₀)
                              (reneq (wkcomp f g) es
                               ≡≡ (rencomp (wk f) (wk g) es))

  Sub≡ : ∀ {Γ Γ'}(f g : TSubst Γ Γ') → Set
  Sub≡ f g = ∀ {A} x → f {A} x ≡ g {A} x

  lifteq : ∀{Γ Γ' A} {f g : TSubst Γ Γ'} → Sub≡ f g → Sub≡ (liftγ {A = A} f) (liftγ g)
  lifteq eq Z = Refl
  lifteq eq (S n) = resp (λ x → ren S x) (eq n)

  -- Prove that applying equal substs produces equal outputs
  subeq : ∀{Γ Γ' A} {f g : TSubst Γ Γ'} → Sub≡ f g → (e : TExp Γ A) → ssubst f e ≡ ssubst g e
  subeq eq (var x) = eq x
  subeq eq (Λ e) = resp Λ (subeq (lifteq eq) e)
  subeq eq (e₁ $ e₂) = resp2 _$_ (subeq eq e₁) (subeq eq e₂)
  subeq eq zero = Refl
  subeq eq (suc e) = resp suc (subeq eq e)
  subeq eq (rec e e₀ es) = resp3 rec (subeq eq e) (subeq eq e₀) (subeq (lifteq eq) es)


  -- Theorems about renaming and substitution
  renwklift : ∀{K Γ Δ C}(f : TRen Γ Δ)(g : TSubst K Γ){A}(x : A ∈ (C :: K)) →
          (ren (wk f) o (liftγ g)) x ≡ liftγ (ren f o g) x
  renwklift f g Z = Refl
  renwklift f g (S n) = symm (rencomp (wk f) S (g n)) ≡≡ rencomp S f (g n)

  rensub : ∀{B Γ Δ}(f : TRen Γ Δ)(g : TSubst B Γ){A}(e : TExp B A) →
          (ren f o ssubst g) e ≡ ssubst (ren f o g) e
  rensub f g (var x) = Refl
  rensub f g (Λ e) = resp Λ ((rensub (wk f) (liftγ g) e) ≡≡
                             subeq (renwklift f g) e)
  rensub f g (e₁ $ e₂) = resp2 _$_ (rensub f g e₁) (rensub f g e₂)
  rensub f g zero = Refl
  rensub f g (suc e) = resp suc (rensub f g e)
  rensub f g (rec e e₀ es) = resp3 rec (rensub f g e) (rensub f g e₀)
                              ((rensub (wk f) (liftγ g) es) ≡≡
                               subeq (renwklift f g) es)

  liftwk : ∀{K Γ Δ C}(f : TSubst Γ Δ)(g : TRen K Γ){A}(x : A ∈ (C :: K)) →
                     (liftγ f o wk g) x ≡ liftγ (f o g) x
  liftwk f g Z = Refl
  liftwk f g (S n) = Refl

  subren : ∀{B Γ Δ}(f : TSubst Γ Δ)(g : TRen B Γ){A}(e : TExp B A) →
          (ssubst f o ren g) e ≡ ssubst (f o g) e
  subren f g (var x) = Refl
  subren f g (Λ e) = resp Λ ((subren (liftγ f) (wk g) e) ≡≡
                             subeq (liftwk f g) e)
  subren f g (e₁ $ e₂) = resp2 _$_ (subren f g e₁) (subren f g e₂)
  subren f g zero = Refl
  subren f g (suc e) = resp suc (subren f g e)
  subren f g (rec e e₀ es) = resp3 rec (subren f g e) (subren f g e₀)
                             ((subren (liftγ f) (wk g) es) ≡≡
                              subeq (liftwk f g) es)

  -- first monad law, the second holds definitionally
  liftid : ∀{Γ A C} (x : A ∈ C :: Γ) → liftγ emptyγ x ≡ emptyγ x
  liftid Z = Refl
  liftid (S n) = Refl

  subid : ∀{Γ}{A} (e : TExp Γ A) → ssubst emptyγ e ≡ id _ e
  subid (var x) = Refl
  subid (Λ e) = resp Λ (subeq liftid e ≡≡ subid e)
  subid (e₁ $ e₂) = resp2 _$_ (subid e₁) (subid e₂)
  subid zero = Refl
  subid (suc e) = resp suc (subid e)
  subid (rec e e₀ es) = resp3 rec (subid e) (subid e₀)
                        (subeq liftid es ≡≡ subid es)


  -- third monad law
  liftcomp : ∀ {B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ) {C A} (x : A ∈ (C :: B)) →
             liftγ (subComp f g) x ≡ (ssubst (liftγ f) o liftγ g) x
  liftcomp f g Z = Refl
  liftcomp f g (S n) = rensub S f (g n) ≡≡ symm (subren (liftγ f) S (g n))

  subcomp : ∀{B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ){A}(t : TExp B A) →
         ssubst (subComp f g) t ≡ (ssubst f o ssubst g) t
  subcomp f g (var x) = Refl
  subcomp f g (Λ e) = resp Λ (subeq (liftcomp f g) e
                              ≡≡ (subcomp (liftγ f) (liftγ g) e))
  subcomp f g (e₁ $ e₂) = resp2 _$_ (subcomp f g e₁) (subcomp f g e₂)
  subcomp f g zero = Refl
  subcomp f g (suc e) = resp suc (subcomp f g e)
  subcomp f g (rec e e₀ es) = resp3 rec (subcomp f g e) (subcomp f g e₀)
                              (subeq (liftcomp f g) es
                               ≡≡ (subcomp (liftγ f) (liftγ g) es))

  -- The lemma about combining substitutions that we are actually
  -- going to need. Being able to prove this lemma was the cause
  -- of most of the grief during this proof.
  combine-subst-noob : ∀ {Γ A C} → (γ : TSubst Γ []) →
                    (e : TExp (A :: Γ) C) →
                    (e' : TCExp A) →
                    ssubst (extendγ γ e') e ≡
                    ssubst (singγ e') (ssubst (liftγ γ) e)
  combine-subst-noob γ e e' = subcomp (singγ e') (liftγ γ) e

  -- A lemma we need to define our relations on substs that respect relns
  extend-nofail-s : ∀{Γ Γ' A B} → (γ : TSubst Γ Γ') → (e : TExp Γ' A) → (n : B ∈ Γ) →
                    γ n ≡ (extendγ γ e) (S n)
  extend-nofail-s γ e n = symm (subren (singγ e) S (γ n) ≡≡ subid (γ n))


  -- A closed subst is the identity
  closed-is-empty : (γ : TSubst [] []) → Sub≡ γ emptyγ
  closed-is-empty γ ()

  -- A substitution made on a closed term is the identity substitution
  closed-subst : ∀{A} → (γ : TSubst [] []) → (e : TCExp A) → ssubst γ e ≡ e
  closed-subst γ e = subeq (closed-is-empty γ) e ≡≡ subid e

  compose-subst-noob : ∀{Γ} {C} → (γ : TSubst Γ []) →
                        (e : TExp Γ C) →
                        {A : TTp} → (x : A ∈ C :: Γ) →
                        subComp (singγ (ssubst γ e)) (liftγ γ) x ≡
                        subComp γ (singγ e) x
  compose-subst-noob γ e Z = Refl
  compose-subst-noob γ e (S x) = subren (singγ (ssubst γ e)) (λ y → S y) (γ x) ≡≡ subid (γ x)


open SubstTheory public
