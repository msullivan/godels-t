module DenotCommutes where

open import Prelude
open import T

---- Proof that dynamic semantics commute with denotational semantics

-- Proving that the dynamic semantics and the denotational semantics
-- commute (if we are using regular equality as our equality in the
-- denotational semantics) basically requires extensionality, since we
-- need to show that things at function type are equal.

-- Since I need extensionality anyways, I use it for things where it isn't
-- as necessary, since it was expedient. My experience in SubstTheory was
-- that it might actually be cleaner to not do that, though.
postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                 (∀ a → f {a} ≡ g {a}) →
                 _≡_ { A = {a : A} → B a} f g

postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                (∀ a → f a ≡ g a) → f ≡ g


module DenotCommutes where

  -- Show that renaming and substitution commute with denotational semantics
  -- in the appropriate sense. This mirrors a bunch of the machinery in SubstTheory.

  -- First stuff for renaming, lifting
  meaning-ren-wk : ∀{A B Γ Γ'} → (γ : TRen Γ Γ') →
                   (η : meaningη Γ') →
                   (a : interp A) →
                   (x : B ∈ A :: Γ) →
                   extendη η a (wk γ x) ≡ extendη (λ y → η (γ y)) a x
  meaning-ren-wk γ η a Z = Refl
  meaning-ren-wk γ η a (S x) = Refl

  meaning-ren : ∀{A Γ Γ'} → (γ : TRen Γ Γ') →
                (e : TExp Γ A) →
                (η : meaningη Γ') →
                meaning (ren γ e) η ≡ meaning e (η o γ)
  meaning-ren γ (var x) η = Refl
  meaning-ren γ (Λ e) η = ext
    (λ a → (meaning-ren (wk γ) e (extendη η a)) ≡≡
           (resp (meaning e) (iext (λ B → ext (λ x → meaning-ren-wk γ η a x)))))
  meaning-ren γ (e $ e') η = resp2 (λ x y → x y) (meaning-ren γ e η) (meaning-ren γ e' η)
  meaning-ren γ zero η = Refl
  meaning-ren γ (suc e) η = resp S (meaning-ren γ e η)
  meaning-ren γ (rec en e0 es) η =
    resp3 NAT.fold
    (meaning-ren γ e0 η)
    (ext (λ _ → ext
                  (λ a →
                     meaning-ren (wk γ) es (extendη η a) ≡≡
                     resp (meaning es)
                     (iext (λ B → ext (λ x → meaning-ren-wk γ η a x))))))
    (meaning-ren γ en η)


  meaning-sub-lift : ∀{A B Γ Γ'} → (γ : TSubst Γ Γ') →
                     (η : meaningη Γ') →
                     (a : interp A) →
                     (x : B ∈ A :: Γ) →
                     meaning (liftγ γ x) (extendη η a) ≡
                     extendη (λ y → meaning (γ y) η) a x
  meaning-sub-lift γ η a Z = Refl
  meaning-sub-lift γ η a (S x) =
    (meaning-ren S (γ x) (extendη η a)) ≡≡
    resp (meaning (γ x)) (iext (λ C → ext (λ x → Refl)))


  -- Define a notion of how to commute a substitution with a
  -- denotational interpretation
  substMeaning : ∀{A Γ Γ'} → (γ : TSubst Γ Γ') →
                 (f : meaningη Γ → interp A) →
                 (meaningη Γ' → interp A)
  substMeaning γ f η = f (λ x → meaning (γ x) η)

  -- And show that that notion actually does commute with it.
  meaning-sub : ∀{A Γ Γ'} → (γ : TSubst Γ Γ') →
                (e : TExp Γ A) →
                (η : meaningη Γ') →
                meaning (ssubst γ e) η ≡ substMeaning γ (meaning e) η
  meaning-sub γ (var x) η = Refl
  meaning-sub γ (Λ e) η = ext
    (λ a → (meaning-sub (liftγ γ) e (extendη η a))
    ≡≡ resp (meaning e) (iext (λ B → ext (λ x → meaning-sub-lift γ η a x))))
  meaning-sub γ (e $ e') η = resp2 (λ x y → x y) (meaning-sub γ e η) (meaning-sub γ e' η)
  meaning-sub γ zero η = Refl
  meaning-sub γ (suc e) η = resp S (meaning-sub γ e η)
  meaning-sub γ (rec en e0 es) η =
   resp3 NAT.fold
   (meaning-sub γ e0 η)
   (ext (λ _ → ext
                 (λ a →
                    meaning-sub (liftγ γ) es (extendη η a) ≡≡
                    resp (meaning es)
                    (iext (λ B → ext (λ x → meaning-sub-lift γ η a x))))))
   (meaning-sub γ en η)

  meaning-sing : ∀{A B}(e' : TCExp B) →
                 (x : A ∈ [ B ]) →
                 meaning (singγ e' x) emptyη ≡ extendη emptyη (meaning e' emptyη) x
  meaning-sing e Z = Refl
  meaning-sing e (S x) = Refl


  -- The basic fact we need about substitution.
  meaning-subst' : ∀{A B}(e' : TCExp B)(e : TExp [ B ] A) →
                  meaning e (extendη emptyη (cmeaning e')) ≡
                  cmeaning (subst e' e)
  meaning-subst' e' e =
    symm (meaning-sub (singγ e') e emptyη ≡≡
         resp (meaning e) (iext (λ A → ext (λ x → meaning-sing e' x))))



  meaning-steps : ∀{A}{e e' : TCExp A} → (e ~> e') → cmeaning e ≡ cmeaning e'
  meaning-steps {e = e₁ $ e₂} (step-app-l St) =
         resp (λ f → f (meaning e₂ emptyη)) (meaning-steps St)
  meaning-steps {e = (Λ e₁) $ e₂} step-beta = meaning-subst' e₂ e₁
  meaning-steps (step-suc St) = resp S (meaning-steps St)
  meaning-steps {e = rec e e₀ es} (step-rec St) =
         resp (λ e' → NAT.fold (meaning e₀ emptyη)
                        (λ n x → meaning es (extendη emptyη x)) e')
              (meaning-steps St)
  meaning-steps step-rec-z = Refl
  meaning-steps {e = rec (suc e) e₀ es} (step-rec-s _) = meaning-subst' (rec e e₀ es) es


open DenotCommutes public
