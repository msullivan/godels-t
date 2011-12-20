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

  subst : ∀{Γ A C} → (Γ' : List TTp) →
          (e' : TExp Γ A) →
          (e : TExp (Γ' ++ A :: Γ) C) →
          TExp (Γ' ++ Γ) C
  subst [] e' (var Z) = e'
  subst [] e' (var (S n)) = var n -- shift up, since we are removing a thing from ctx
  subst (_ :: Γ') e' (var Z) = var Z
  subst (_ :: Γ') e' (var (S n)) = 
    weaken LIST.SET.sub-cons (subst Γ' e' (var n))
  subst Γ' e' (Λ e) = Λ (subst (_ :: Γ') e' e)
  subst Γ' e' (e₁ $ e₂) = (subst Γ' e' e₁) $ (subst Γ' e' e₂)
  subst Γ' e' zero = zero

  -- could I use just a list? (yes, but not if I want an intrinsic encoding?)
  {-
  data TSubst (Γ : List TTp) : List TTp → Set where
    [] : TSubst Γ []
    _::_ : ∀{A Γ'} → (e' : TExp Γ A) → (γ : TSubst Γ Γ') → TSubst Γ (A :: Γ')
  -}
  TSubst : (Γ : List TTp) -> List TTp → Set
  TSubst Γ Γ' = ∀{A} (x : A ∈ Γ') -> TExp Γ A

  emptyγ : ∀{Γ} -> TSubst Γ []
  emptyγ ()

  extendγ : ∀{Γ Γ' A} -> TSubst Γ Γ' -> TExp Γ A -> TSubst Γ (A :: Γ')
  extendγ γ e Z = e
  extendγ γ e (S n) = γ n


  ssubst : ∀{Γ Γ'' C} → (Γ' : List TTp) →
           (γ : TSubst Γ Γ'') →
           (e : TExp (Γ' ++ Γ'' ++ Γ) C) →
           TExp (Γ' ++ Γ) C
  ssubst {Γ} {Γ''} [] γ (var x) with LIST.split-append {xs = Γ''} x
  ... | Inl y = γ y
  ... | Inr y = var y
  ssubst (_ :: Γ') γ (var Z) = var Z
  ssubst (_ :: Γ') γ (var (S n)) = weaken LIST.SET.sub-cons (ssubst Γ' γ (var n))
  ssubst Γ' γ (Λ e) = Λ (ssubst (_ :: Γ') γ e)
  ssubst Γ' γ (e₁ $ e₂) = (ssubst Γ' γ e₁) $ (ssubst Γ' γ e₂)
  ssubst Γ' γ zero = zero

  subst1 : ∀{Γ A C} → (Γ' : List TTp) →
           (e' : TExp Γ A) →
           (e : TExp (Γ' ++ A :: Γ) C) →
           TExp (Γ' ++ Γ) C
  subst1 Γ' e' e = ssubst Γ' (extendγ emptyγ e') e

{-
  ssubst [] e' (var Z) = e'
  ssubst [] e' (var (S n)) = var n -- shift up, since we are removing a thing from ctx
  ssubst (_ :: Γ') e' (var Z) = var Z
  ssubst (_ :: Γ') e' (var (S n)) = 
    weaken LIST.SET.sub-cons (ssubst Γ' e' (var n))
  ssubst Γ' e' (Λ e) = Λ (ssubst (_ :: Γ') e' e)
  ssubst Γ' e' (e₁ $ e₂) = (ssubst Γ' e' e₁) $ (ssubst Γ' e' e₂)
  ssubst Γ' e' zero = zero
-}


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


{-
  -- extend HT to substitutions
  HTg : (Γ : List TTp) → TSubst Γ → Set
  HTg [] [] = ⊤
  HTg (A :: Γ) (e :: γ) = (HT A e) × (HTg Γ γ)

  -- the main theorem
  all-HT : ∀{Γ A γ} → (e : TExp Γ A) → HTg Γ γ → HT A (ssubst γ e)
  all-HT (var x) H = {!!}
  all-HT (Λ e) H = {!!}
  all-HT (e₁ $ e₂) H = {!!}
  all-HT zero H = halts {!!} val-zero
-}
