module SubstTheory where

open import Prelude
open import T

-- We could avoid needing to do this, but it would be a pain in the
-- ass.  We would have to do a lot of passing around of proofs that
-- substitutions behave the same.  It's easier to just use postulated
-- extensional equivalence to convert those proofs into full
-- equality proofs.
postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                 (∀ a → f {a} ≡ g {a}) →
                 _≡_ { A = {a : A} → B a} f g

postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                (∀ a → f a ≡ g a) → f ≡ g

---- (Lots of theory. *Lots*. Too much. Sigh.)

module SubstTheory where

  renext : ∀ {Γ Γ'}{f g : TRen Γ Γ'} → (∀ {A} x → f {A} x ≡ g {A} x) → _≡_ {A = TRen Γ Γ'} f g
  renext f = iext (λ _ → ext f)

  -- Some theorems about renamings
  wkid : ∀{Γ A C} (x : A ∈ C :: Γ) → wk renId x ≡ renId x
  wkid Z = Refl
  wkid (S n) = Refl

  renid : ∀{Γ A} (e : TExp Γ A) → ren renId e ≡ id _ e
  renid (var x) = Refl
  renid (Λ e) = resp Λ (resp (λ (f : TRen _ _) → ren f e) 
                              (renext wkid)
                        ≡≡ renid e)
  renid (e₁ $ e₂) = resp2 _$_ (renid e₁) (renid e₂)
  renid zero = Refl
  renid (suc e) = resp suc (renid e)
  renid (rec e e₀ es) = resp3 rec (renid e) (renid e₀)
                        (resp (λ (f : TRen _ _) → ren f es)
                              (renext wkid)
                          ≡≡ renid es)

  wkcomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {C A} (x : A ∈ (C :: B)) →
             wk (renComp f g) x ≡ (wk f o wk g) x
  wkcomp f g Z = Refl
  wkcomp f g (S n) = Refl

  rencomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {A} (e : TExp B A) →
             ren (renComp f g) e ≡ (ren f o ren g) e
  rencomp f g (var x) = Refl
  rencomp f g (Λ e) = resp Λ (resp (λ (f : TRen _ _) → ren f e) 
                              (renext (wkcomp f g))
                              ≡≡ (rencomp (wk f) (wk g) e))
  rencomp f g (e₁ $ e₂) = resp2 _$_ (rencomp f g e₁) (rencomp f g e₂)
  rencomp f g zero = Refl
  rencomp f g (suc e) = resp suc (rencomp f g e)
  rencomp f g (rec e e₀ es) = resp3 rec (rencomp f g e) (rencomp f g e₀)
                              (resp (λ (f : TRen _ _) → ren f es) 
                               (renext (wkcomp f g))
                               ≡≡ (rencomp (wk f) (wk g) es))


  subext : ∀ {Γ Γ'}{f g : TSubst Γ Γ'} → (∀ {A} x → f {A} x ≡ g {A} x) → _≡_ {A = TSubst Γ Γ'} f g
  subext f = iext (λ _ → ext f)

  -- Theorems about renaming and substitution
  renwklift : ∀{K Γ Δ C}(f : TRen Γ Δ)(g : TSubst K Γ){A}(x : A ∈ (C :: K)) →
          (ren (wk f) o (liftγ g)) x ≡ liftγ (ren f o g) x
  renwklift f g Z = Refl
  renwklift f g (S n) = symm (rencomp (wk f) S (g n)) ≡≡ rencomp S f (g n)

  rensub : ∀{B Γ Δ}(f : TRen Γ Δ)(g : TSubst B Γ){A}(e : TExp B A) →
          (ren f o ssubst g) e ≡ ssubst (ren f o g) e
  rensub f g (var x) = Refl
  rensub f g (Λ e) = resp Λ ((rensub (wk f) (liftγ g) e) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f e)
                              (subext (renwklift f g)))
  rensub f g (e₁ $ e₂) = resp2 _$_ (rensub f g e₁) (rensub f g e₂)
  rensub f g zero = Refl
  rensub f g (suc e) = resp suc (rensub f g e)
  rensub f g (rec e e₀ es) = resp3 rec (rensub f g e) (rensub f g e₀)
                              ((rensub (wk f) (liftγ g) es) ≡≡ 
                               resp (λ (f : TSubst _ _) → ssubst f es)
                               (subext (renwklift f g)))

  liftwk : ∀{K Γ Δ C}(f : TSubst Γ Δ)(g : TRen K Γ){A}(x : A ∈ (C :: K)) →
                     (liftγ f o wk g) x ≡ liftγ (f o g) x
  liftwk f g Z = Refl
  liftwk f g (S n) = Refl

  subren : ∀{B Γ Δ}(f : TSubst Γ Δ)(g : TRen B Γ){A}(e : TExp B A) →
          (ssubst f o ren g) e ≡ ssubst (f o g) e
  subren f g (var x) = Refl
  subren f g (Λ e) = resp Λ ((subren (liftγ f) (wk g) e) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f e)
                              (subext (liftwk f g)))
  subren f g (e₁ $ e₂) = resp2 _$_ (subren f g e₁) (subren f g e₂)
  subren f g zero = Refl
  subren f g (suc e) = resp suc (subren f g e)
  subren f g (rec e e₀ es) = resp3 rec (subren f g e) (subren f g e₀)
                             ((subren (liftγ f) (wk g) es) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f es)
                              (subext (liftwk f g)))

  -- first monad law, the second holds definitionally
  liftid : ∀{Γ A C} (x : A ∈ C :: Γ) → liftγ emptyγ x ≡ emptyγ x
  liftid Z = Refl
  liftid (S n) = Refl

  subid : ∀{Γ}{A} (e : TExp Γ A) → ssubst emptyγ e ≡ id _ e
  subid (var x) = Refl
  subid (Λ e) = resp Λ (resp (λ (f : TSubst _ _) → ssubst f e) (subext liftid) ≡≡ subid e)
  subid (e₁ $ e₂) = resp2 _$_ (subid e₁) (subid e₂)
  subid zero = Refl
  subid (suc e) = resp suc (subid e)
  subid (rec e e₀ es) = resp3 rec (subid e) (subid e₀)
                        (resp (λ (f : TSubst _ _) → ssubst f es) (subext liftid) ≡≡ subid es)


  -- third monad law
  liftcomp : ∀ {B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ) {C A} (x : A ∈ (C :: B)) →
             liftγ (subComp f g) x ≡ (ssubst (liftγ f) o liftγ g) x
  liftcomp f g Z = Refl
  liftcomp f g (S n) = rensub S f (g n) ≡≡ symm (subren (liftγ f) S (g n))

  subcomp : ∀{B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ){A}(t : TExp B A) →
         ssubst (subComp f g) t ≡ (ssubst f o ssubst g) t
  subcomp f g (var x) = Refl
  subcomp f g (Λ e) = resp Λ ((resp (λ (f : TSubst _ _) → ssubst f e) 
                              (subext (liftcomp f g)))
                              ≡≡ (subcomp (liftγ f) (liftγ g) e))
  subcomp f g (e₁ $ e₂) = resp2 _$_ (subcomp f g e₁) (subcomp f g e₂)
  subcomp f g zero = Refl
  subcomp f g (suc e) = resp suc (subcomp f g e)
  subcomp f g (rec e e₀ es) = resp3 rec (subcomp f g e) (subcomp f g e₀)
                              ((resp (λ (f : TSubst _ _) → ssubst f es) 
                               (subext (liftcomp f g)))
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

  extend-nofail-s : ∀{Γ Γ' A B} → (γ : TSubst Γ Γ') → (e : TExp Γ' A) → (n : B ∈ Γ) →
                    (extendγ γ e) (S n) ≡ γ n
  extend-nofail-s γ e n = subren (singγ e) S (γ n) ≡≡ subid (γ n)

open SubstTheory public
