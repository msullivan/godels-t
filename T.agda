module T where

open import Prelude

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

-- Gödel's T
module GÖDEL-T where

  data TTp : Set where
    nat : TTp
    _⇒_ : (A B : TTp) -> TTp

  data TExp (Γ : List TTp) : TTp -> Set where
    var : ∀{A} (x : A ∈ Γ) -> TExp Γ A
    Λ : ∀{A B} (e : TExp (A :: Γ) B) -> TExp Γ (A ⇒ B)
    _$_ : ∀{A B} (e₁ : TExp Γ (A ⇒ B)) (e₂ : TExp Γ A) -> TExp Γ B
    zero : TExp Γ nat

  weaken : ∀{Γ Γ' B} -> (Γ ⊆ Γ') -> TExp Γ B -> TExp Γ' B
  weaken s (var x) = var (s x)
  weaken s (Λ e) = Λ (weaken (LIST.SET.sub-cons-congr s) e)
  weaken s (e₁ $ e₂) = weaken s e₁ $ weaken s e₂
  weaken s zero = zero

  subst : ∀{Γ A C} -> (Γ' : List TTp) ->
          (e' : TExp Γ A) ->
          (e : TExp (Γ' ++ A :: Γ) C) ->
          TExp (Γ' ++ Γ) C
  subst [] e' (var Z) = e'
  subst [] e' (var (S n)) = var n -- shift up, since we are removing a thing from ctx
  subst (_ :: Γ') e' (var Z) = var Z
  subst (_ :: Γ') e' (var (S n)) = 
    weaken LIST.SET.sub-cons (subst Γ' e' (var n))
  subst Γ' e' (Λ e) = Λ (subst (_ :: Γ') e' e)
  subst Γ' e' (e₁ $ e₂) = (subst Γ' e' e₁) $ (subst Γ' e' e₂)
  subst Γ' e' zero = zero

  data TVal : {A : TTp} -> TExp [] A -> Set where
    val-zero : TVal zero
    val-lam : {A B : TTp} {e : TExp (A :: []) B} -> TVal (Λ e)

  -- only worry about closed steps; embed preservation in the statement
  data _~>_ : {A : TTp} -> TExp [] A -> TExp [] A -> Set where
    step-app-l : {A B : TTp} {e₁ e₁' : TExp [] (A ⇒ B)} {e₂ : TExp [] A} -> 
                  e₁ ~> e₁' -> (e₁ $ e₂) ~> (e₁' $ e₂)
    step-app-r : {A B : TTp} {e₁ : TExp [] (A ⇒ B)} {e₂ e₂' : TExp [] A} -> 
                  TVal e₁ -> e₂ ~> e₂' -> (e₁ $ e₂) ~> (e₁ $ e₂')
    step-beta  : {A B : TTp} {e : TExp (A :: []) B} {e' : TExp [] A} ->
                  TVal e' ->
                  ((Λ e) $ e') ~> (subst [] e' e)

  data _~>*_ : {A : TTp} -> TExp [] A -> TExp [] A -> Set where
    eval-refl : {A : TTp} {e : TExp [] A} -> e ~>* e
    eval-cons : {A : TTp} {e e' e'' : TExp [] A} ->
               e ~> e' -> e' ~>* e'' -> e ~>* e''

  data TProgress : {A : TTp} -> TExp [] A -> Set where
    prog-val : {A : TTp} {e : TExp [] A} -> TVal e -> TProgress e
    prog-step : {A : TTp} {e e' : TExp [] A} -> e ~> e' -> TProgress e

  
  progress : {A : TTp} (e : TExp [] A) -> TProgress e
  progress (var ())
  progress (Λ e) = prog-val val-lam
  progress (e₁ $ e₂) with progress e₁
  progress (e₁ $ e₂) | prog-step D = prog-step (step-app-l D)
  progress (.(Λ e) $ e₂) | prog-val (val-lam {_} {_} {e}) with progress e₂
  ... | prog-val D = prog-step (step-beta D)
  ... | prog-step D' = prog-step (step-app-r val-lam D')
  progress zero = prog-val val-zero
