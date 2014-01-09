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

  -- prove that we can life any compatibility rule from steps to eval
  eval-compat : ∀{A B} {P : TCExp A -> TCExp B} →
                 (∀{e e'} → (e ~> e' → P e ~> P e')) →
                 {e e' : TCExp A} → e ~>* e' → P e ~>* P e'
  eval-compat f eval-refl = eval-refl
  eval-compat f (eval-cons S1 D) = eval-cons (f S1) (eval-compat f D)

  -- Lemma we need to prove determism
  not-val-and-step : ∀{C : Set} {A : TTp} {e e' : TCExp A} →
                     TVal e → e ~> e' →
                     C
  not-val-and-step val-zero ()
  not-val-and-step val-lam ()
  not-val-and-step (val-suc v) (step-suc S1) = not-val-and-step v S1

  -- Show that the dynamic semantics are a function
  step-deterministic : ∀{A} → (e : TCExp A) → {e' e'' : TCExp A} →
                       e ~> e' → e ~> e'' ->
                       e' ≡ e''
  -- Trivial contradictory cases
  step-deterministic (var x) () S2
  step-deterministic (Λ e) () S2
  step-deterministic zero () S2
  step-deterministic (Λ e $ e') step-beta (step-app-l ())
  step-deterministic (Λ e $ e') (step-app-l ()) step-beta
  step-deterministic (rec .zero e'' e₂) (step-rec ()) step-rec-z
  step-deterministic (rec zero e₀ es) step-rec-z (step-rec ())

  -- Nontrival contradictory cases
  step-deterministic (rec (suc e) e₁ e₂) (step-rec (step-suc S1)) (step-rec-s v) = not-val-and-step v S1
  step-deterministic (rec (suc e) e₁ e₂) (step-rec-s v) (step-rec (step-suc S2)) = not-val-and-step v S2

  -- Normal cases
  step-deterministic (e $ e') (step-app-l S1) (step-app-l S2) =
                   resp (λ x → x $ e') (step-deterministic e S1 S2)
  step-deterministic (Λ e $ e') step-beta step-beta = Refl
  step-deterministic (suc e) (step-suc S1) (step-suc S2) = resp suc (step-deterministic e S1 S2)
  step-deterministic (rec e e₁ e₂) (step-rec S1) (step-rec S2) =
                    resp (λ x → rec x e₁ e₂) (step-deterministic e S1 S2)
  step-deterministic (rec zero _ _) step-rec-z step-rec-z = Refl
  step-deterministic (rec (suc e) e₁ e₂) (step-rec-s x) (step-rec-s x₁) = Refl

  -- Prove that if we evaluate to two expressions, and one is a value,
  -- then the other evaluates to it.
  eval-finish : ∀{A} → {e : TCExp A} → {e' e'' : TCExp A} →
                e ~>* e' → e ~>* e'' →
                TVal e'' →
                e' ~>* e''
  eval-finish eval-refl E2 v = E2
  eval-finish (eval-cons S1 E1) eval-refl v = not-val-and-step v S1
  eval-finish (eval-cons S1 E1) (eval-cons S2 E2) v with step-deterministic _ S1 S2
  ... | Refl = eval-finish E1 E2 v

  -- Prove that if we evaluate to two values, they are the same
  eval-deterministic : ∀{A} → {e : TCExp A} → {e' e'' : TCExp A} →
                       e ~>* e' → e ~>* e'' →
                       TVal e' → TVal e'' →
                       e' ≡ e''
  eval-deterministic E1 E2 v1 v2 with eval-finish E1 E2 v2
  ... | eval-refl = Refl
  ... | eval-cons S1 _ = not-val-and-step v1 S1

open DynTheory public
