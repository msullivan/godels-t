module Progress where

open import Prelude
open import T

---- progress

module Progress where
  -- Define a datatype representing that a term satisfies progress
  data TProgress : ∀{A} → TCExp A → Set where
    prog-val : ∀{A} {e : TCExp A} → (D : TVal e) → TProgress e
    prog-step : ∀{A} {e e' : TCExp A} → (D : e ~> e') → TProgress e

  -- prove that all terms satisfy progress
  progress : ∀{A} (e : TCExp A) → TProgress e
  progress (var ())
  progress (Λ e) = prog-val val-lam
  progress (e₁ $ e₂) with progress e₁
  progress (e₁ $ e₂) | prog-step D = prog-step (step-app-l D)
  progress (.(Λ e) $ e₂) | prog-val (val-lam {_} {_} {e}) with progress e₂
  ... | prog-val D = prog-step step-beta
  ... | prog-step D' = prog-step (step-app-r D')
  progress zero = prog-val val-zero
  progress (suc e) with progress e
  ... | prog-val D = prog-val (val-suc D)
  ... | prog-step D' = prog-step (step-suc D')
  progress (rec e e₀ es) with progress e
  progress (rec .zero e₀ es) | prog-val val-zero = prog-step step-rec-z
  progress (rec .(suc e) e₀ es) | prog-val (val-suc {e} y) = prog-step step-rec-s
  ... | prog-step D = prog-step (step-rec D)


open Progress public
