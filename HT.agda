module HT where

open import Prelude
open import T
open import SubstTheory
open import DynTheory


module HT where

  ---- Halting and Hereditary Termination
  -- Should I use a record, or the product thing, or something else?
  data THalts : ∀{A} → TCExp A → Set where
    halts : {A : TTp} {e e' : TCExp A} → (eval : (e ~>* e')) → (val : TVal e') → THalts e

  -- An old comment about lhs-halt

  -- Mostly for fun, I didn't want to include "and it halts" as part
  -- of the definition of HT for arrows, and I didn't want to define
  -- it in terms of evaluating to a lambda and then substituting.
  -- This seems to require being able to generate an inhabitant of an
  -- arbitrary type as well as a proof that it is HT. The former is
  -- easy in T and we accomplish the latter by appealing to all-HT,
  -- although we could have also generated the proof along with the
  -- inhabitant.  This all seems to be handwaved away when doing it on
  -- paper. Things get more unclear when in a system where not all
  -- types are inhabited; if we know that either a type is inhabited or
  -- it is not, then we are fine. But since we are constructive, we would
  -- get tripped up by a language like System F in which type inhabitability
  -- is undecidable. (Of course, the proof is easy to repair in a number of
  -- ways by modifying the definition of HT.)
  --
  -- When I went to make the system deterministic, I found that I now depended
  -- on HT-halts in all-HT, which broke the previous proof technique.
  -- I decided that proving the inhabitant we construct is HT would be
  -- annoying, so I decided to not bother and went back to hanging onto the
  -- proof that arrows halt.

  -- Extract that the lhs must halt if its application to something halts.
  -- I think this isn't actually useful, though, since to use it we would
  -- need to be able to produce an argument to the function.
  lhs-halt : {A B : TTp} {e : TCExp (A ⇒ B)} {e' : TCExp A} →
              THalts (e $ e') → THalts e
  lhs-halt (halts eval-refl ())
  lhs-halt (halts (eval-cons (step-app-l S1) E) val) with lhs-halt (halts E val)
  ... | halts E' val' = halts (eval-cons S1 E') val'
  lhs-halt (halts (eval-cons step-beta E) val) = halts eval-refl val-lam

  -- I think the induction principle for this datatype is the definition of
  -- HTω from http://www.cs.cmu.edu/~rwh/courses/typesys/hw3/hw3-handout.pdf
  data HTω : TNat → Set where
    HT-z : {e : TNat} → (E : e ~>* zero) → HTω e
    HT-s : {e e' : TNat} → (E : e ~>* suc e') → (HT : HTω e') → HTω e

  -- definition of hereditary termination
  HT : (A : TTp) → TCExp A → Set
  HT nat e = THalts e
  -- It is kind of ugly to have to hang on to the halting proof.
  HT (A ⇒ B) e = THalts e × ((e' : TCExp A) → HT A e' → HT B (e $ e'))

  -- proof that hereditary termination implies termination
  HT-halts : ∀{A} → (e : TCExp A) → HT A e → THalts e
  HT-halts {nat} e h = h
  HT-halts {A ⇒ B} _ (h , _) = h


  -- extend HT to substitutions
  HTΓ : (Γ : Ctx) → TSubst Γ [] → Set
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) -> HT A (γ x)

  emptyHTΓ : ∀{γ : TSubst [] []} -> HTΓ [] γ
  emptyHTΓ ()

  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ []} ->
              HTΓ Γ γ -> HT A e -> HTΓ (A :: Γ) (extendγ γ e)
  extendHTΓ η ht Z = ht
  extendHTΓ {_} {_} {e} {γ} η ht {B} (S n) =
             ID.coe1 (HT B) (extend-nofail-s γ e n) (η n)

  -- head expansion lemma
  head-expansion : ∀{A} {e e' : TCExp A} → (e ~>* e') → HT A e' → HT A e
  head-expansion {nat} eval (halts eval₁ val) = halts (eval-trans eval eval₁) val
  head-expansion {A ⇒ B} eval (halts eval' val , ht-logic) =
     halts (eval-trans eval eval') val ,
     (λ e' ht → head-expansion (eval-compat step-app-l eval) (ht-logic e' ht))

  -- the main theorem
  all-HT : ∀{Γ A} {γ : TSubst Γ []} → (e : TExp Γ A) → HTΓ Γ γ
            → HT A (ssubst γ e)
  all-HT (var x) η = η x
  all-HT (e₁ $ e₂) η with all-HT e₁ η
  ... | _ , HT₁ = HT₁ (ssubst _ e₂) (all-HT e₂ η)
  all-HT zero η = halts eval-refl val-zero
  all-HT (suc e) η with all-HT e η
  ... | halts eval val = halts (eval-compat step-suc eval) (val-suc val)

  all-HT {Γ} {A ⇒ B} {γ} (Λ e) η =
    (halts eval-refl val-lam) ,
     lam-case
    where lam-case : (e' : TCExp A) → HT A e' → HT B (Λ (ssubst (liftγ γ) e) $ e')
          lam-case e' ht' with all-HT {γ = extendγ γ e'} e (extendHTΓ η ht')
          ... | ht with eval-step (step-beta {e = (ssubst (liftγ γ) e)})
          ... | steps-full with combine-subst-noob γ e e'
          ... | eq = head-expansion steps-full (ID.coe1 (HT B) eq ht)

  all-HT {Γ} {A} {γ} (rec e e₀ es) η with all-HT e η
  ... | halts E val = head-expansion (eval-compat step-rec E) (inner val)
    where inner : {n : TNat} → TVal n → HT A (rec n (ssubst γ e₀) (ssubst (liftγ γ) es))
          inner val-zero = head-expansion (eval-step step-rec-z) (all-HT e₀ η)
          inner (val-suc v) with all-HT es (extendHTΓ η (inner v))
          ... | ht with eval-step (step-rec-s v)
          ... | steps with combine-subst-noob γ es _
          ... | eq = head-expansion steps (ID.coe1 (HT A) eq ht)

  -- Prove that all programs in Gödel's System T halt.
  all-halt : ∀{A} → (e : TCExp A) → THalts e
  all-halt {A} e = HT-halts e (ID.coe1 (HT A) (subid e) (all-HT e (emptyHTΓ {emptyγ})))

open HT public
