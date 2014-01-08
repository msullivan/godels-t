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


open DynTheory public
