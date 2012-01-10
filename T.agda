module T where

open import Prelude

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

-- Gödel's T
module GÖDEL-T where

  -- Core syntax
  infixr 5 _⇒_
  infixl 5 _$_
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

  ---- definition and theory related to substitution
  weaken : ∀{Γ Γ' B} → (Γ ⊆ Γ') → TExp Γ B → TExp Γ' B
  weaken s (var x) = var (s x)
  weaken s (Λ e) = Λ (weaken (LIST.SET.sub-cons-congr s) e)
  weaken s (e₁ $ e₂) = weaken s e₁ $ weaken s e₂
  weaken s zero = zero
  weaken s (suc e) = suc (weaken s e)
  weaken s (rec e e₀ es) = rec (weaken s e) (weaken s e₀)
                           (weaken (LIST.SET.sub-cons-congr s) es)

  data TSubst : Ctx → Ctx → Set where
    [] : ∀{Γ} → TSubst [] Γ
    _::_ : ∀{Γ Γ' A} → (e : TExp Γ' A) → (γ : TSubst Γ Γ') → TSubst (A :: Γ) Γ'

  infixr 5 _+++_
  _+++_ : ∀{Γ Γ' D} → TSubst Γ D → TSubst Γ' D → TSubst (Γ ++ Γ') D
  [] +++ γ' = γ'
  (e :: γ) +++ γ' = e :: (γ +++ γ')


  emptyγ : ∀{Γ} → TSubst [] Γ
  emptyγ = []

  extendγ : ∀{Γ Γ' A} → (e : TExp Γ' A) → (γ : TSubst Γ Γ') → TSubst (A :: Γ) Γ'
  extendγ = _::_

  weakenγ : ∀{Γ Γ' Γ''} → (Γ' ⊆ Γ'') → TSubst Γ Γ' → TSubst Γ Γ''
  weakenγ s [] = []
  weakenγ s (e :: γ) = weaken s e :: weakenγ s γ


  lookup : ∀{A Γ Γ'} → TSubst Γ Γ' → (x : A ∈ Γ) → TExp Γ' A
  lookup [] ()
  lookup (e :: _) Z = e
  lookup (_ :: es) (S n) = lookup es n

  self-extendγ : ∀{Γ Γ' A} → TSubst Γ Γ' → TSubst (A :: Γ) (A :: Γ')
  self-extendγ γ = (var Z) :: (weakenγ LIST.SET.sub-cons γ)

  self-extend-nγ : ∀{Γ Γ'} → (Γ'' : Ctx) → TSubst Γ Γ' → TSubst (Γ'' ++ Γ) (Γ'' ++ Γ')
  self-extend-nγ [] γ = γ
  self-extend-nγ (A :: Γ'') γ = self-extendγ (self-extend-nγ Γ'' γ)


  ssubst : ∀{Γ Γ' C} →
           (γ : TSubst Γ Γ') →
           (e : TExp Γ C) →
           TExp Γ' C
  ssubst γ (var x) = lookup γ x
  ssubst γ (Λ e) = Λ (ssubst (self-extendγ γ) e)
  ssubst γ (e₁ $ e₂) = (ssubst γ e₁) $ (ssubst γ e₂)
  ssubst γ zero = zero
  ssubst γ (suc e) = suc (ssubst γ e)
  ssubst γ (rec e e₀ es) = rec (ssubst γ e) (ssubst γ e₀) (ssubst (self-extendγ γ) es)

  compγ : ∀{Γ Γ' Γ''} → TSubst Γ Γ' → TSubst Γ'' Γ → TSubst Γ'' Γ'
  compγ γ [] = []
  compγ γ (e :: γ') = ssubst γ e :: (compγ γ γ')


  -- substituting one closed thing
  subst : ∀{A C} →
          (e' : TCExp A) →
          (e : TExp (A :: []) C) →
          TCExp C
  subst e' e = ssubst (e' :: []) e

{-
  -- combining lemma
  combine-subst : ∀ {A Γ C} {γ : TSubst Γ} →
                    (Γ' : Ctx) →
                    (e : TExp (Γ' ++ A :: Γ) C) →
                    (e' : TCExp A) →
                    ssubst Γ' (e' :: [])
                      (ssubst (Γ' ++ A :: []) γ (ID.coe1 (λ x → TExp x C) {!!} e)) ≡
                      ssubst Γ' (e' :: γ) e
  combine-subst = {!!}
-}

{-

  combine-subst : ∀ {Γ Γ' Γ'' C} → (γ : TSubst Γ Γ') →
                    (γ' : TSubst Γ'' Γ) →
                    (e : TExp Γ'' C) →
                    ssubst γ (ssubst γ' e) ≡
                    ssubst (compγ γ γ') e
  combine-subst γ γ' (var x) = {!!}
  combine-subst γ γ' (Λ e) with resp Λ (combine-subst (self-extendγ γ) (self-extendγ γ') e)
  ... | ass = {!!}
  combine-subst γ γ' (e₁ $ e₂) = resp2 _$_ (combine-subst γ γ' e₁) (combine-subst γ γ' e₂)
  combine-subst γ γ' zero = Refl

  another-bs-lemma : ∀ {A C Γ} →
                    (e' : TExp Γ A) →
                    (e : TExp Γ C) →
                    e ≡ ssubst (e' :: self-extend-nγ {!Γ!} []) (weaken (λ {x} → S) {!!})
  another-bs-lemma e' e = {!!}

  some-bs-lemma : ∀ {Γ A} → (γ : TSubst Γ []) →
                  (e' : TCExp A) →
                  γ ≡ (compγ (e' :: []) (weakenγ (λ {x} → S) γ))
  some-bs-lemma [] e' = Refl
  some-bs-lemma (e :: γ) e' = resp2 _::_ {!!} (some-bs-lemma γ e')

  combine-subst-noob : ∀ {Γ A C} → (γ : TSubst Γ []) →
                    (e : TExp (A :: Γ) C) →
                    (e' : TCExp A) →
                    ssubst (extendγ e' emptyγ) (ssubst (self-extendγ γ) e) ≡
                    ssubst (extendγ e' γ) e
  combine-subst-noob γ e e' with combine-subst (e' :: []) (self-extendγ γ) e
  ... | ass = {!!}

-}

  postulate
    combine-subst-noob : ∀ {Γ A C} → (γ : TSubst Γ []) →
                       (e : TExp (A :: Γ) C) →
                       (e' : TCExp A) →
                       ssubst (extendγ e' emptyγ) (ssubst (self-extendγ γ) e) ≡
                       ssubst (extendγ e' γ) e


  ---- dynamic semantics (and, implicitly, preservation)
  data TVal : ∀{A} → TCExp A → Set where
    val-zero : TVal zero
    val-suc : ∀{e} → TVal e → TVal (suc e)
    val-lam : ∀{A B} {e : TExp (A :: []) B} → TVal (Λ e)

  -- only worry about closed steps; embed preservation in the statement
  -- the evaluation semantics are non-deterministic; we could get rid of step-app-r
  data _~>_ : ∀{A} → TCExp A → TCExp A → Set where
    step-app-l : ∀{A B} {e₁ e₁' : TCExp (A ⇒ B)} {e₂ : TCExp A} →
                  e₁ ~> e₁' → (e₁ $ e₂) ~> (e₁' $ e₂)
    step-app-r : ∀{A B} {e₁ : TCExp (A ⇒ B)} {e₂ e₂' : TCExp A} →
                  e₂ ~> e₂' → (e₁ $ e₂) ~> (e₁ $ e₂')
    step-beta  : ∀{A B} {e : TExp (A :: []) B} {e' : TCExp A} →
                  ((Λ e) $ e') ~> (subst e' e)
    step-suc   : ∀{e e' : TCExp nat} →
                  e ~> e' → (suc e) ~> (suc e')
    step-rec   : ∀{A} {e e' : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  e ~> e' → (rec e e₀ es) ~> (rec e' e₀ es)
    step-rec-z : ∀{A} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  (rec zero e₀ es) ~> e₀
    step-rec-s : ∀{A} {e : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                  (rec (suc e) e₀ es) ~> subst (rec e e₀ es) es


  ---- progress
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


  ---- iterated stepping, and theorems about it
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

  eval-rec   : ∀{A} {e e' : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} →
                e ~>* e' → (rec e e₀ es) ~>* (rec e' e₀ es)
  eval-rec eval-refl = eval-refl
  eval-rec (eval-cons S1 D) = eval-cons (step-rec S1) (eval-rec D)

  eval-suc   : {e e' : TCExp nat} →
                e ~>* e' → suc e ~>* suc e'
  eval-suc eval-refl = eval-refl
  eval-suc (eval-cons S1 D) = eval-cons (step-suc S1) (eval-suc D)


  ---- Halting and Hereditary Termination
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

  -- I think the induction principle for this datatype is the definition of
  -- HTω from the homework.
  data HTω : TNat → Set where
    HT-z : {e : TNat} → (E : e ~>* zero) → HTω e
    HT-s : {e e' : TNat} → (E : e ~>* suc e') → (HT : HTω e') → HTω e

  -- definition of hereditary termination
  HT : (A : TTp) → TCExp A → Set
  HT nat e = HTω e
  -- I'm a bit dubious about the "THalts e"
  HT (A ⇒ B) e = THalts e × ((e' : TCExp A) → HT A e' → HT B (e $ e'))

  -- proof that hereditary termination implies termination
  HT-halts : ∀{A} → (e : TCExp A) → HT A e → THalts e
  HT-halts {nat} e (HT-z E) = halts E val-zero
  HT-halts {nat} e (HT-s {.e} {e'} E HT) with HT-halts e' HT
  ... | halts eval val = halts (eval-trans E (eval-suc eval)) (val-suc val)
  HT-halts {A ⇒ B} _ (h , _) = h


  -- extend HT to substitutions
  HTΓ : (Γ : Ctx) → TSubst Γ [] → Set
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) → HT A (lookup γ x)

  emptyHTΓ : ∀{η : TSubst [] []} → HTΓ [] η
  emptyHTΓ ()

  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ []} →
              HTΓ Γ γ → HT A e → HTΓ (A :: Γ) (extendγ e γ)
  extendHTΓ η HT Z = HT
  extendHTΓ η HT (S n) = η n

  -- head expansion lemma
  head-expansion : ∀{A} {e e' : TCExp A} → (e ~>* e') → HT A e' → HT A e
  head-expansion {nat} eval (HT-z E) = HT-z (eval-trans eval E)
  head-expansion {nat} eval (HT-s E HT) = HT-s (eval-trans eval E) HT
  head-expansion {A ⇒ B} eval (halts eval' val , ht-logic) =
     halts (eval-trans eval eval') val ,
     (λ e' ht → head-expansion (eval-app-l eval) (ht-logic e' ht))


  -- the main theorem
  all-HT : ∀{Γ A} {γ : TSubst Γ []} → (e : TExp Γ A) → HTΓ Γ γ
            → HT A (ssubst γ e)
  all-HT (var x) η = η x
  all-HT (e₁ $ e₂) η with all-HT e₁ η
  ... | _ , HT₁ = HT₁ (ssubst _ e₂) (all-HT e₂ η)
  all-HT zero η = HT-z eval-refl
  all-HT (suc e) η = HT-s eval-refl (all-HT e η)

  all-HT {Γ} {A ⇒ B} {γ} (Λ e) η =
    (halts eval-refl val-lam) ,
     lam-case
    where lam-case : (e' : TCExp A) → HT A e' → HT B (Λ (ssubst (self-extendγ γ) e) $ e')
          lam-case e' ht' with all-HT {γ = extendγ e' γ} e (extendHTΓ η ht')
          ... | ht with eval-step step-beta
          ... | steps-full with combine-subst-noob γ e _
          ... | eq = head-expansion
                    (ID.coe1 (λ x → (Λ (ssubst (self-extendγ γ) e) $ e') ~>* x) eq steps-full) ht

  all-HT {Γ} {A} {γ} (rec e e₀ es) η = inner (all-HT e η)
    where inner : {e : TNat} → HTω e → HT A (rec e (ssubst γ e₀) (ssubst (self-extendγ γ) es))
          inner (HT-z E) with eval-trans (eval-rec {es = (ssubst (self-extendγ γ) es)} E)
                              (eval-step step-rec-z)
          ... | steps-full = head-expansion steps-full (all-HT e₀ η)
          inner {e} (HT-s E ht') with all-HT {γ = extendγ _ γ} es (extendHTΓ η (inner ht'))
          ... | ht with eval-trans (eval-rec {e₀ = (ssubst γ e₀)} E) (eval-step step-rec-s)
          ... | steps-full with combine-subst-noob γ es _
          ... | eq = head-expansion
                      (ID.coe1 (λ x → (rec e (ssubst γ e₀) (ssubst (self-extendγ γ) es)) ~>* x)
                               eq steps-full)
                      ht

{-
  all-halt : ∀{A} → (e : TCExp A) → THalts e
  all-halt e with all-HT e emptyHTΓ
  ... | ht with (empty-subst-nop e)
  ... | eq = {!eq!}
-}

  ---- some example programs
  -- boy, de bruijn indexes are unreadable
  wk : ∀{Γ B} → TCExp B → TExp Γ B
  wk e = weaken (LIST.SET.sub-appendr [] _) e

  one : TNat
  one = suc zero
  two = suc one
  three = suc two
  t-plus : TCExp (nat ⇒ nat ⇒ nat)
  t-plus = Λ (Λ (rec (var (S Z)) (var Z) (suc (var Z))))
  t-compose : ∀{A B C} → TCExp ((A ⇒ B) ⇒ (C ⇒ A) ⇒ (C ⇒ B))
  t-compose = Λ (Λ (Λ (var (S (S Z)) $ ((var (S Z)) $ (var Z)))))
  t-id : ∀{A} → TCExp (A ⇒ A)
  t-id = Λ (var Z)
  t-iterate : ∀{A} → TCExp (nat ⇒ (A ⇒ A) ⇒ (A ⇒ A))
  t-iterate = Λ (Λ (rec (var (S Z)) (wk t-id)
                     (wk t-compose $ var (S Z) $ var Z)))
  t-ack : TCExp (nat ⇒ nat ⇒ nat)
  t-ack = Λ (rec (var Z) (Λ (suc (var Z)))
              (Λ (wk t-iterate $ var Z $ var (S Z) $ (var (S Z) $ wk one))))


open GÖDEL-T public
