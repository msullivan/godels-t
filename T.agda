module T where

open import Prelude

module GÖDEL-T where

  -- Core syntax
  infixr 30 _⇒_
  infixl 30 _$_
  data TTp : Set where
    nat : TTp
    _⇒_ : (A B : TTp) → TTp

  Ctx = List TTp

  data TExp (Γ : Ctx) : TTp → Set where
    var : ∀{A} (x : A ∈ Γ) → TExp Γ A
    Λ : ∀{A B} (e : TExp (A :: Γ) B) → TExp Γ (A ⇒ B)
    _$_ : ∀{A B} (e₁ : TExp Γ (A ⇒ B)) (e₂ : TExp Γ A) → TExp Γ B
    zero : TExp Γ nat
    suc : (e : TExp Γ nat) → TExp Γ nat
    rec : ∀{A} → (e : TExp Γ nat) → (e₀ : TExp Γ A) → (es : TExp (A :: Γ) A) →
               TExp Γ A

  TCExp = TExp []
  TNat = TCExp nat

  ---- denotational semantics
  interp : TTp → Set
  interp nat = Nat
  interp (A ⇒ B) = interp A → interp B

  meaningη : (Γ : Ctx) → Set
  meaningη Γ = ∀{A} (x : A ∈ Γ) → interp A

  emptyη : meaningη []
  emptyη ()

  extendη : ∀{Γ A} → meaningη Γ → interp A → meaningη (A :: Γ)
  extendη η M Z = M
  extendη η M (S n) = η n

  meaning : ∀{A Γ} → TExp Γ A → meaningη Γ → interp A
  meaning (var x) η = η x
  meaning (Λ e) η = λ x → meaning e (extendη η x)
  meaning (e₁ $ e₂) η = meaning e₁ η (meaning e₂ η)
  meaning zero η = Z
  meaning (suc e) η = S (meaning e η)
  meaning (rec e e₀ es) η = NAT.fold (meaning e₀ η)
                                     (λ n x → meaning es (extendη η x))
                                     (meaning e η)

  cmeaning : ∀{A} → TCExp A → interp A
  cmeaning e = meaning e emptyη

  ---- Definition related to substitution.
  -- Renamings
  TRen : Ctx → Ctx → Set
  TRen Γ Γ' = ∀ {A} → A ∈ Γ → A ∈ Γ'

  renId : ∀{Γ} → TRen Γ Γ
  renId = \ x -> x

  renComp : ∀{B Γ Δ} → TRen Γ Δ → TRen B Γ → TRen B Δ
  renComp f g = f o g

  wk : ∀{Γ Γ' A} → TRen Γ Γ' → TRen (A :: Γ) (A :: Γ')
  wk f Z = Z
  wk f (S n) = S (f n)

  ren : ∀{Γ Γ'} → TRen Γ Γ' → ∀ {A} → TExp Γ A → TExp Γ' A
  ren γ (var x) = var (γ x)
  ren γ (Λ e) = Λ (ren (wk γ) e)
  ren γ (e₁ $ e₂) = (ren γ e₁) $ (ren γ e₂)
  ren γ zero = zero
  ren γ (suc e) = suc (ren γ e)
  ren γ (rec e e₀ es) = rec (ren γ e) (ren γ e₀) (ren (wk γ) es)

  -- Substitutions
  TSubst : Ctx → Ctx → Set
  TSubst Γ Γ' = ∀ {A} → A ∈ Γ → TExp Γ' A

  emptyγ : ∀{Γ} → TSubst Γ Γ
  emptyγ = λ x → var x

  liftγ : ∀{Γ Γ' A} → TSubst Γ Γ' → TSubst (A :: Γ) (A :: Γ')
  liftγ γ Z = var Z
  liftγ γ (S n) = ren S (γ n)

  singγ : ∀{Γ A} → TExp Γ A → TSubst (A :: Γ) Γ
  singγ e Z = e
  singγ e (S n) = var n

  dropγ : ∀{Γ A Γ'} → TSubst (A :: Γ) Γ' → TSubst Γ Γ'
  dropγ γ n = γ (S n)

  closed-wkγ : {Γ : Ctx} → TRen [] Γ
  closed-wkγ ()

  ssubst : ∀{Γ Γ' C} →
           (γ : TSubst Γ Γ') →
           (e : TExp Γ C) →
           TExp Γ' C
  ssubst γ (var x) = γ x
  ssubst γ (Λ e) = Λ (ssubst (liftγ γ) e)
  ssubst γ (e₁ $ e₂) = (ssubst γ e₁) $ (ssubst γ e₂)
  ssubst γ zero = zero
  ssubst γ (suc e) = suc (ssubst γ e)
  ssubst γ (rec e e₀ es) = rec (ssubst γ e) (ssubst γ e₀) (ssubst (liftγ γ) es)

  subComp : ∀{B Γ Γ'} → TSubst Γ Γ' → TSubst B Γ → TSubst B Γ'
  subComp f g = ssubst f o g

  extendγ : ∀{Γ Γ' A} → TSubst Γ Γ' → TExp Γ' A → TSubst (A :: Γ) Γ'
  extendγ γ e = subComp (singγ e) (liftγ γ)


  -- substituting one thing in a closed term
  subst : ∀{A C} → (e' : TCExp A) → (e : TExp (A :: []) C) → TCExp C
  subst e' e = ssubst (singγ e') e

  weaken-closed : ∀{Γ B} → TCExp B → TExp Γ B
  weaken-closed e = ren closed-wkγ e

  ---- dynamic semantics (and, implicitly, preservation)
  data TVal : ∀{Γ A} → TExp Γ A → Set where
    val-zero : ∀{Γ} → TVal {Γ} zero
    val-suc : ∀{Γ e} → TVal {Γ} e → TVal {Γ} (suc e)
    val-lam : ∀{A B} {e : TExp (A :: []) B} → TVal (Λ e)

  -- only worry about closed steps; embed preservation in the statement
  -- We are call-by-name for function application, but call-by-value for natural evaluation.
  -- This is so that any value of type nat is a numeral.
  data _~>_ : ∀{A} → TCExp A → TCExp A → Set where
    step-app-l : ∀{A B} {e₁ e₁' : TCExp (A ⇒ B)} {e₂ : TCExp A} →
                  e₁ ~> e₁' → (e₁ $ e₂) ~> (e₁' $ e₂)
    step-beta  : ∀{A B} {e : TExp (A :: []) B} {e' : TCExp A} →
                  ((Λ e) $ e') ~> (subst e' e)
    step-suc   : ∀{e e' : TCExp nat} →
                  e ~> e' → (suc e) ~> (suc e')
    step-rec   : ∀{A} {e e' : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  e ~> e' → (rec e e₀ es) ~> (rec e' e₀ es)
    step-rec-z : ∀{A} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  (rec zero e₀ es) ~> e₀
    step-rec-s : ∀{A} {e : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  TVal e → (rec (suc e) e₀ es) ~> subst (rec e e₀ es) es

  -- iterated stepping
  data _~>*_ : ∀{A} → TCExp A → TCExp A → Set where
    eval-refl : ∀{A} {e : TCExp A} → e ~>* e
    eval-cons : ∀{A} {e e' e'' : TCExp A} →
               e ~> e' → e' ~>* e'' → e ~>* e''

  eval-step : ∀{A} {e e' : TCExp A} → e ~> e' → e ~>* e'
  eval-step s = eval-cons s eval-refl

  -- Should I use a record, or the product thing, or something else?
  data THalts : ∀{A} → TCExp A → Set where
    halts : {A : TTp} {e e' : TCExp A} → (eval : (e ~>* e')) → (val : TVal e') → THalts e

open GÖDEL-T public
