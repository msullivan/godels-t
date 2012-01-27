module DynTheory where

open import Prelude
open import T

---- Some theory about the dynamic semantics

module DynTheory where

  -- prove some obvious theorems about iterated stepping
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

  eval-app-r : ∀{A B} {e₂ e₂' : TCExp A} → (e₁ : TCExp (A ⇒ B)) →
                e₂ ~>* e₂' → (e₁ $ e₂) ~>* (e₁ $ e₂')
  eval-app-r _ eval-refl = eval-refl
  eval-app-r _ (eval-cons S1 D) = eval-cons (step-app-r S1) (eval-app-r _ D)

  eval-rec   : ∀{A} {e e' : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                e ~>* e' → (rec e e₀ es) ~>* (rec e' e₀ es)
  eval-rec eval-refl = eval-refl
  eval-rec (eval-cons S1 D) = eval-cons (step-rec S1) (eval-rec D)

  eval-suc   : {e e' : TCExp nat} →
                e ~>* e' → suc e ~>* suc e'
  eval-suc eval-refl = eval-refl
  eval-suc (eval-cons S1 D) = eval-cons (step-suc S1) (eval-suc D)



open DynTheory public
