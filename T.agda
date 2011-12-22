module T where

open import Prelude

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

-- Gödel's T
module GÖDEL-T where

  data TTp : Set where
    nat : TTp
    _⇒_ : (A B : TTp) → TTp

  data TExp (Γ : List TTp) : TTp → Set where
    var : ∀{A} (x : A ∈ Γ) → TExp Γ A
    Λ : ∀{A B} (e : TExp (A :: Γ) B) → TExp Γ (A ⇒ B)
    _$_ : ∀{A B} (e₁ : TExp Γ (A ⇒ B)) (e₂ : TExp Γ A) → TExp Γ B
    zero : TExp Γ nat

  TCExp = TExp []

  weaken : ∀{Γ Γ' B} → (Γ ⊆ Γ') → TExp Γ B → TExp Γ' B
  weaken s (var x) = var (s x)
  weaken s (Λ e) = Λ (weaken (LIST.SET.sub-cons-congr s) e)
  weaken s (e₁ $ e₂) = weaken s e₁ $ weaken s e₂
  weaken s zero = zero

  -- substitutions
  TSubst : List TTp → Set
  TSubst Γ = ∀{A} (x : A ∈ Γ) -> TCExp A

  emptyγ : TSubst []
  emptyγ ()

  extendγ : ∀{Γ A} -> TSubst Γ -> TCExp A -> TSubst (A :: Γ)
  extendγ γ e Z = e
  extendγ γ e (S n) = γ n


  ssubst : ∀{Γ C} → (Γ' : List TTp) →
           (γ : TSubst Γ) →
           (e : TExp (Γ' ++ Γ) C) →
           TExp (Γ') C
  ssubst [] γ (var x) = γ x
  ssubst (_ :: Γ') γ (var Z) = var Z
  ssubst (_ :: Γ') γ (var (S n)) = weaken LIST.SET.sub-cons (ssubst Γ' γ (var n))
  ssubst Γ' γ (Λ e) = Λ (ssubst (_ :: Γ') γ e)
  ssubst Γ' γ (e₁ $ e₂) = (ssubst Γ' γ e₁) $ (ssubst Γ' γ e₂)
  ssubst Γ' γ zero = zero


  -- substituting one thing
  subst : ∀{A C} → (Γ' : List TTp) →
          (e' : TCExp A) →
          (e : TExp (Γ' ++ A :: []) C) →
          TExp (Γ') C
  subst Γ' e' e = ssubst Γ' (extendγ emptyγ e') e



  -- dynamic semantics
  data TVal : ∀{A} → TCExp A → Set where
    val-zero : TVal zero
    val-lam : ∀{A B} {e : TExp (A :: []) B} → TVal (Λ e)

  -- only worry about closed steps; embed preservation in the statement
  data _~>_ : ∀{A} → TCExp A → TCExp A → Set where
    step-app-l : ∀{A B } {e₁ e₁' : TCExp (A ⇒ B)} {e₂ : TCExp A} → 
                  e₁ ~> e₁' → (e₁ $ e₂) ~> (e₁' $ e₂)
    step-app-r : ∀{A B} {e₁ : TCExp (A ⇒ B)} {e₂ e₂' : TCExp A} → 
                  TVal e₁ → e₂ ~> e₂' → (e₁ $ e₂) ~> (e₁ $ e₂')
    step-beta  : ∀{A B} {e : TExp (A :: []) B} {e' : TCExp A} →
                  TVal e' →
                  ((Λ e) $ e') ~> (subst [] e' e)

  -- Define a datatype representing that a term satisfies progress
  data TProgress : ∀{A} → TCExp A → Set where
    prog-val : ∀{A} {e : TCExp A} → TVal e → TProgress e
    prog-step : ∀{A} {e e' : TCExp A} → e ~> e' → TProgress e

  -- prove that all terms satisfy progress
  progress : ∀{A} (e : TCExp A) → TProgress e
  progress (var ())
  progress (Λ e) = prog-val val-lam
  progress (e₁ $ e₂) with progress e₁
  progress (e₁ $ e₂) | prog-step D = prog-step (step-app-l D)
  progress (.(Λ e) $ e₂) | prog-val (val-lam {_} {_} {e}) with progress e₂
  ... | prog-val D = prog-step (step-beta D)
  ... | prog-step D' = prog-step (step-app-r val-lam D')
  progress zero = prog-val val-zero



  -- define iterated stepping...
  data _~>*_ : ∀{A} → TCExp A → TCExp A → Set where
    eval-refl : ∀{A} {e : TCExp A} → e ~>* e
    eval-cons : ∀{A} {e e' e'' : TCExp A} →
               e ~> e' → e' ~>* e'' → e ~>* e''

  -- and prove some obvious theorems about it
  -- transitivity (which makes sense, given that it is the transitive closure)
  eval-trans : ∀{A} {e e' e'' : TCExp A} →
                e ~>* e' → e' ~>* e'' → e ~>* e''
  eval-trans eval-refl E2 = E2
  eval-trans (eval-cons S1 E1') E2 = eval-cons S1 (eval-trans E1' E2)

  -- stupid compatibility rules that lift the step compat rules to
  -- the eval level
  eval-app-l : ∀{A B} {e₁ e₁' : TCExp (A ⇒ B)} {e₂ : TCExp A} → 
                e₁ ~>* e₁' → (e₁ $ e₂) ~>* (e₁' $ e₂)
  eval-app-l eval-refl = eval-refl
  eval-app-l (eval-cons S1 D) = eval-cons (step-app-l S1) (eval-app-l D)

  eval-app-r : ∀{A B} {e₁ : TCExp (A ⇒ B)} {e₂ e₂' : TCExp A} → 
                TVal e₁ → e₂ ~>* e₂' → (e₁ $ e₂) ~>* (e₁ $ e₂')
  eval-app-r V eval-refl = eval-refl
  eval-app-r V (eval-cons S1 D) = eval-cons (step-app-r V S1) (eval-app-r V D)

  -- Should I use a record, or the product thing, or something else?
  data THalts : ∀{A} → TCExp A → Set where
    halts : {A : TTp} {e e' : TCExp A} → (e ~>* e') → TVal e' → THalts e

  -- extract that the lhs must halt if its application to something halts
  lhs-halt : {A B : TTp} {e : TCExp (A ⇒ B)} {e' : TCExp A} → 
              THalts (e $ e') → THalts e
  lhs-halt (halts eval-refl ())
  lhs-halt (halts (eval-cons (step-app-l S1) E) V) with lhs-halt (halts E V)
  ... | halts E' V' = halts (eval-cons S1 E') V'
  lhs-halt (halts (eval-cons (step-app-r V1 S2) E) V2) = halts eval-refl V1
  lhs-halt (halts (eval-cons (step-beta V1) E) V2) = halts eval-refl val-lam


  -- definition of hereditary termination
  HT : (A : TTp) → TCExp A → Set
  HT nat e = THalts e -- this is actually for unit, of course
  -- I'm a bit dubious about the "THalts e"
  HT (A ⇒ B) e = THalts e × ((e' : TCExp A) → HT A e' → HT B (e $ e'))

  -- proof that hereditary termination implies termination
  HT-halts : ∀{A e} → HT A e → THalts e
  HT-halts {nat} h = h
  HT-halts {A ⇒ B} (h , _) = h

  -- extend HT to substitutions
  HTΓ : (Γ : List TTp) → TSubst Γ → Set
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) -> HT A (γ x)

  emptyHTΓ : ∀{η : TSubst []} -> HTΓ [] η
  emptyHTΓ ()

  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ} ->
              HTΓ Γ γ -> HT A e -> HTΓ (A :: Γ) (extendγ γ e)
  extendHTΓ η HT Z = HT
  extendHTΓ η HT (S n) = η n

  -- the main theorem
  all-HT : ∀{Γ A} {γ : TSubst Γ} → (e : TExp Γ A) → HTΓ Γ γ
            → HT A (ssubst [] γ e)
  all-HT (var x) η = {!!}
  all-HT (Λ e) η = {!!}
  all-HT (e₁ $ e₂) η = {!!}
  all-HT zero η = halts eval-refl val-zero
