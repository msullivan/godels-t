module DenotCommutes where

open import Prelude
open import T

---- Proof that dynamic semantics commute with denotational semantics

module DenotCommutes where

  -- Proving that the dynamic semantics and the denotational semantics
  -- commute (at least if we are using regular equality as our
  -- equality for interpreted terms) basically requires
  -- extensionality, since we need to show that things at function
  -- type are equal.
  postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                   (∀ a → f {a} ≡ g {a}) →
                   _≡_ { A = {a : A} → B a} f g

  postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                  (∀ a → f a ≡ g a) → f ≡ g


  -- Show that renaming and substitution commute with denotational semantics
  -- in the appropriate sense. This mirrors a bunch of the machinery in SubstTheory.

  -- Some equality related stuff

  Meaning≡ : ∀ {Γ}(f g : meaningη Γ) → Set
  Meaning≡ f g = ∀ {A} x → f {A} x ≡ g {A} x

  -- These are extensionality like lemmas. I feel like they are usually nicer
  -- to use than actually using extensionality.
  -- They could be proven legitimately but we have ext and I am feeling lazy.
  meaningeq : ∀{Γ A} {f g : meaningη Γ} → Meaning≡ f g → (e : TExp Γ A) →
               meaning e f ≡ meaning e g
  meaningeq eq e = resp (meaning e) (iext (λ B → ext (λ x → eq x)))

  foldeq : ∀{A} {a0 a0' : A} {an an' : Nat} {as as' : Nat → A → A} →
           a0 ≡ a0' →
           ((n : Nat) (x : A) → as n x ≡ as' n x) →
           an ≡ an' →
           NAT.fold a0 as an ≡ NAT.fold a0' as' an'
  foldeq eq0 eqs eqn = resp3 NAT.fold eq0 (ext (λ n → ext (λ a → eqs n a))) eqn

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
  meaning-ren γ (Λ e) η =
    ext (λ M →
     meaning-ren (wk γ) e (extendη η M) ≡≡ meaningeq (meaning-ren-wk γ η M) e)
  meaning-ren γ (e $ e') η = resp2 (λ x y → x y) (meaning-ren γ e η) (meaning-ren γ e' η)
  meaning-ren γ zero η = Refl
  meaning-ren γ (suc e) η = resp S (meaning-ren γ e η)
  meaning-ren γ (rec en e0 es) η =
    foldeq
     (meaning-ren γ e0 η)
     (λ _ M → meaning-ren (wk γ) es (extendη η M) ≡≡ meaningeq (meaning-ren-wk γ η M) es)
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
  meaning-sub γ (Λ e) η =
    ext (λ M →
      meaning-sub (liftγ γ) e (extendη η M) ≡≡ meaningeq (meaning-sub-lift γ η M) e)
  meaning-sub γ (e $ e') η = resp2 (λ x y → x y) (meaning-sub γ e η) (meaning-sub γ e' η)
  meaning-sub γ zero η = Refl
  meaning-sub γ (suc e) η = resp S (meaning-sub γ e η)
  meaning-sub γ (rec en e0 es) η =
   foldeq
   (meaning-sub γ e0 η)
   (λ _ M → meaning-sub (liftγ γ) es (extendη η M) ≡≡ meaningeq (meaning-sub-lift γ η M) es)
   (meaning-sub γ en η)

  -- Easy lemma about singleton contexts
  meaning-sing : ∀{A B}(e' : TCExp B) →
                 (x : A ∈ [ B ]) →
                 meaning (singγ e' x) emptyη ≡ extendη emptyη (meaning e' emptyη) x
  meaning-sing e Z = Refl
  meaning-sing e (S x) = Refl


  -- The basic fact we need about substitution.
  meaning-subst : ∀{A B}(e' : TCExp B)(e : TExp [ B ] A) →
                  meaning e (extendη emptyη (cmeaning e')) ≡
                  cmeaning (subst e' e)
  meaning-subst e' e =
    symm (meaning-sub (singγ e') e emptyη ≡≡
          resp (meaning e) (iext (λ A → ext (λ x → meaning-sing e' x))))


  -- The main theorem about the dynamic semantics
  meaning-steps : ∀{A}{e e' : TCExp A} → (e ~> e') → cmeaning e ≡ cmeaning e'
  meaning-steps {e = e₁ $ e₂} (step-app-l St) =
         resp (λ f → f (meaning e₂ emptyη)) (meaning-steps St)
  meaning-steps {e = (Λ e₁) $ e₂} step-beta = meaning-subst e₂ e₁
  meaning-steps (step-suc St) = resp S (meaning-steps St)
  meaning-steps {e = rec e e₀ es} (step-rec St) =
         resp (λ e' → NAT.fold (meaning e₀ emptyη)
                        (λ n x → meaning es (extendη emptyη x)) e')
              (meaning-steps St)
  meaning-steps step-rec-z = Refl
  meaning-steps {e = rec (suc e) e₀ es} (step-rec-s _) = meaning-subst (rec e e₀ es) es


  meaning-eval : ∀{A}{e e' : TCExp A} → (e ~>* e') → cmeaning e ≡ cmeaning e'
  meaning-eval eval-refl = Refl
  meaning-eval (eval-cons S1 E) = meaning-steps S1 ≡≡ meaning-eval E

open DenotCommutes public
