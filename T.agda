module T where

open import Prelude

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

concats : ∀{A : Set} → List (List A) → List A
concats [] = []
concats (xs :: xss) = xs ++ concats xss

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
  data TSubst : List TTp → Set where
    [] : TSubst []
    _::_ : ∀{Γ A} → TCExp A → TSubst Γ → TSubst (A :: Γ)

  lookup : ∀{A Γ} -> TSubst Γ -> (x : A ∈ Γ) -> TCExp A
  lookup [] ()
  lookup (e :: _) Z = e
  lookup (_ :: es) (S n) = lookup es n

  infixr 5 _+++_
  _+++_ : ∀{Γ Γ'} → TSubst Γ → TSubst Γ' → TSubst (Γ ++ Γ')
  [] +++ γ' = γ'
  (e :: γ) +++ γ' = e :: (γ +++ γ')
  
  ssubst : ∀{Γ C} → (Γ' : List TTp) →
           (γ : TSubst Γ) →
           (e : TExp (Γ' ++ Γ) C) →
           TExp (Γ') C
  ssubst [] γ (var x) = lookup γ x
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
  subst Γ' e' e = ssubst Γ' (e' :: []) e

  -- combining lemma
  -- I'm really kind of worried about this.
  combine-subst : ∀ {Γ Γ' C} {γ : TSubst Γ} →
                    (Γ'' : List TTp) →
                    (e : TExp (Γ'' ++ Γ' ++ Γ) C) →
                    (γ' : TSubst Γ') → 
                    ssubst Γ'' γ' (ssubst (Γ'' ++ Γ') γ 
                         (ID.coe1 (λ x → TExp x C) (LIST.assoc-append {as = Γ''}) e)) ≡
                    ssubst Γ'' (γ' +++ γ) e
  combine-subst Γ'' e γ' = {!!}

  combine-subst-noob : ∀ {Γ A C} → (γ : TSubst Γ) →
                    (e : TExp (A :: Γ) C) →
                    (e' : TCExp A) →
                    ssubst [] (e' :: []) (ssubst [ A ] γ e) ≡
                    ssubst [] (e' :: γ) e
  combine-subst-noob _ e e' = combine-subst [] e (e' :: [])

  --empty-subst-nop : ∀{A Γ} → (e : TExp Γ A) → e ≡ ssubst Γ [] e
  --empty-subst-nop : ∀{A} → (e : TCExp A) → e ≡ ssubst [] [] e
  --empty-subst-nop = {!!}

{-
  -- combining lemma
  combine-subst : ∀ {A Γ C} {γ : TSubst Γ} →
                    (Γ' : List TTp) →
                    (e : TExp (Γ' ++ A :: Γ) C) →
                    (e' : TCExp A) → 
                    ssubst Γ' (e' :: []) 
                      (ssubst (Γ' ++ A :: []) γ (ID.coe1 (λ x → TExp x C) {!!} e)) ≡
                      ssubst Γ' (e' :: γ) e
  combine-subst = {!!}
-}
{-
  combine-subst Γ' (var Z) e' = Refl
  combine-subst {A} {.[]} {C} {[]} Γ' (var (S ())) e'
  combine-subst {A} {.(_ :: _)} {C} {y :: y'} Γ' (var (S n)) e' = {!!}
  combine-subst Γ' (Λ e) e' = resp1 Λ {!!}
  combine-subst Γ' (e₁ $ e₂) e' = resp2 _$_ (combine-subst Γ' e₁ e') (combine-subst Γ' e₂ e')
  combine-subst Γ' zero e' = Refl
-}
  -- dynamic semantics
  data TVal : ∀{A} → TCExp A → Set where
    val-zero : TVal zero
    val-lam : ∀{A B} {e : TExp (A :: []) B} → TVal (Λ e)

  -- only worry about closed steps; embed preservation in the statement
  -- the evaluation semantics are non-deterministic; we could get rid of step-app-r
  data _~>_ : ∀{A} → TCExp A → TCExp A → Set where
    step-app-l : ∀{A B} {e₁ e₁' : TCExp (A ⇒ B)} {e₂ : TCExp A} → 
                  e₁ ~> e₁' → (e₁ $ e₂) ~> (e₁' $ e₂)
    step-app-r : ∀{A B} {e₁ : TCExp (A ⇒ B)} {e₂ e₂' : TCExp A} → 
                  e₂ ~> e₂' → (e₁ $ e₂) ~> (e₁ $ e₂')
    step-beta  : ∀{A B} {e : TExp (A :: []) B} {e' : TCExp A} →
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
  ... | prog-val D = prog-step step-beta
  ... | prog-step D' = prog-step (step-app-r D')
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

  eval-step : ∀{A} {e e' : TCExp A} → e ~> e' → e ~>* e'
  eval-step s = eval-cons s eval-refl

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


  -- Should I use a record, or the product thing, or something else?
  data THalts : ∀{A} → TCExp A → Set where
    halts : {A : TTp} {e e' : TCExp A} → (eval : (e ~>* e')) → (val : TVal e') → THalts e

  -- extract that the lhs must halt if its application to something halts
{-
  lhs-halt : {A B : TTp} {e : TCExp (A ⇒ B)} {e' : TCExp A} → 
              THalts (e $ e') → THalts e
  lhs-halt (halts eval-refl ())
  lhs-halt (halts (eval-cons (step-app-l S1) E) V) with lhs-halt (halts E V)
  ... | halts E' V' = halts (eval-cons S1 E') V'
  lhs-halt (halts (eval-cons (step-app-r V1 S2) E) V2) = halts eval-refl V1
  lhs-halt (halts (eval-cons (step-beta V1) E) V2) = halts eval-refl val-lam
-}

  -- definition of hereditary termination
  HT : (A : TTp) → TCExp A → Set
  HT nat e = THalts e -- this is actually for unit, of course
  -- I'm a bit dubious about the "THalts e"
  HT (A ⇒ B) e = THalts e × ((e' : TCExp A) → HT A e' → HT B (e $ e'))

  -- proof that hereditary termination implies termination
  HT-halts : ∀{A} → (e : TCExp A) → HT A e → THalts e
  HT-halts {nat} _ h = h
  HT-halts {A ⇒ B} _ (h , _) = h


  -- extend HT to substitutions
  HTΓ : (Γ : List TTp) → TSubst Γ → Set
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) -> HT A (lookup γ x)

  emptyHTΓ : ∀{η : TSubst []} -> HTΓ [] η
  emptyHTΓ ()


  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ} ->
              HTΓ Γ γ -> HT A e -> HTΓ (A :: Γ) (e :: γ)
  extendHTΓ η HT Z = HT
  extendHTΓ η HT (S n) = η n

  head-expansion : ∀{A} {e e' : TCExp A} -> (e ~>* e') -> HT A e' -> HT A e
  head-expansion {nat} eval (halts eval' val) = halts (eval-trans eval eval') val
  head-expansion {A ⇒ B} eval (halts eval' val , ht-logic) =
     halts (eval-trans eval eval') val ,
     (λ e' ht → head-expansion (eval-app-l eval) (ht-logic e' ht))


  mutual
    lam-case : ∀ {A B Γ} {γ : TSubst Γ} → (e : TExp (A :: Γ) B) → HTΓ Γ γ →
                 (e' : TCExp A) → HT A e' → HT B (Λ (ssubst (A :: []) γ e) $ e')
    lam-case {A} {B} {Γ} {γ} e η e' ht' with all-HT {γ = e' :: γ} e (extendHTΓ η ht')
    ... | ht with eval-step step-beta
    ... | steps-full with combine-subst-noob γ e _
    ... | eq = head-expansion
               (ID.coe1 (λ x → (Λ (ssubst (A :: []) γ e) $ e') ~>* x) eq steps-full) ht

    -- the main theorem
    all-HT : ∀{Γ A} {γ : TSubst Γ} → (e : TExp Γ A) → HTΓ Γ γ
              → HT A (ssubst [] γ e)
    all-HT (var x) η = η x
    all-HT (Λ e) η = 
      (halts eval-refl val-lam) , 
       lam-case e η
    all-HT (e₁ $ e₂) η with all-HT e₁ η
    ... | _ , HT₁ = HT₁ (ssubst [] _ e₂) (all-HT e₂ η)
    all-HT zero η = halts eval-refl val-zero

{-
  all-halt : ∀{A} → (e : TCExp A) → THalts e
  all-halt e with all-HT e emptyHTΓ
  ... | ht with (empty-subst-nop e)
  ... | eq = {!eq!}
-}
