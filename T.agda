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

  weaken : ∀{Γ Γ' B} → (Γ ⊆ Γ') → TExp Γ B → TExp Γ' B
  weaken s (var x) = var (s x)
  weaken s (Λ e) = Λ (weaken (LIST.SET.sub-cons-congr s) e)
  weaken s (e₁ $ e₂) = weaken s e₁ $ weaken s e₂
  weaken s zero = zero
  weaken s (suc e) = suc (weaken s e)
  weaken s (rec e e₀ es) = rec (weaken s e) (weaken s e₀)
                           (weaken (LIST.SET.sub-cons-congr s) es)

  -- substitutions
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


  lookup : ∀{A Γ Γ'} -> TSubst Γ Γ' -> (x : A ∈ Γ) -> TExp Γ' A
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


  -- dynamic semantics
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

  eval-rec   : ∀{A} {e e' : TCExp nat} {e₀ : TCExp A} {es : TExp (A :: []) A} → 
                e ~>* e' → (rec e e₀ es) ~>* (rec e' e₀ es)
  eval-rec eval-refl = eval-refl
  eval-rec (eval-cons S1 D) = eval-cons (step-rec S1) (eval-rec D)


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

  Predω = TNat -> Set
  HTPredω = Σ[ P :: Predω ] (∀{e} → e ~>* zero → P e) ×
                            (∀{e e'} → e ~>* (suc e') → P e' → P e)
  HTω : TNat -> Set1
  HTω e = (P : HTPredω) → fst P e

  -- definition of hereditary termination
  HT : (A : TTp) → TCExp A → Set1
  HT nat e = HTω e --THalts e -- this is actually for unit, of course
  -- I'm a bit dubious about the "THalts e"
  HT (A ⇒ B) e = THalts e × ((e' : TCExp A) → HT A e' → HT B (e $ e'))

  -- proof that hereditary termination implies termination
  HT-halts : ∀{A} → (e : TCExp A) → HT A e → THalts e
  HT-halts {nat} _ h = {!!}
  HT-halts {A ⇒ B} _ (h , _) = h

  HTω' : TNat -> Set1
  HTω' e = (e ~>* zero) + (Σ[ e' :: TNat ] (e ~>* suc e' × HTω e'))
  
  HTω'-imp-HTω : {e : TNat} → HTω' e → HTω e
  HTω'-imp-HTω (Inl E) (_ , zP , _) = zP E
  HTω'-imp-HTω (Inr (e' , E , H)) (P , zP , sP) =
                sP E (H (P , zP , sP))

  -- extend HT to substitutions
  HTΓ : (Γ : Ctx) → TSubst Γ [] → Set1
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) -> HT A (lookup γ x)

  emptyHTΓ : ∀{η : TSubst [] []} -> HTΓ [] η
  emptyHTΓ ()

  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ []} ->
              HTΓ Γ γ -> HT A e -> HTΓ (A :: Γ) (extendγ e γ)
  extendHTΓ η HT Z = HT
  extendHTΓ η HT (S n) = η n


  head-expansion : ∀{A} {e e' : TCExp A} -> (e ~>* e') -> HT A e' -> HT A e
--  head-expansion {nat} eval (halts eval' val) = halts (eval-trans eval eval') val
  head-expansion {nat} eval _ = {!!}
  head-expansion {A ⇒ B} eval (halts eval' val , ht-logic) =
     halts (eval-trans eval eval') val ,
     (λ e' ht → head-expansion (eval-app-l eval) (ht-logic e' ht))


  mutual
    lam-case : ∀ {A B Γ} {γ : TSubst Γ []} → (e : TExp (A :: Γ) B) → HTΓ Γ γ →
                 (e' : TCExp A) → HT A e' → HT B (Λ (ssubst (self-extendγ γ) e) $ e')
    lam-case {A} {B} {Γ} {γ} e η e' ht' with all-HT {γ = extendγ e' γ} e (extendHTΓ η ht')
    ... | ht with eval-step step-beta
    ... | steps-full with combine-subst-noob γ e _
    ... | eq = head-expansion
               (ID.coe1 (λ x → (Λ (ssubst (self-extendγ γ) e) $ e') ~>* x) eq steps-full) ht

    -- the main theorem
    all-HT : ∀{Γ A} {γ : TSubst Γ []} → (e : TExp Γ A) → HTΓ Γ γ
              → HT A (ssubst γ e)
    all-HT (var x) η = η x
    all-HT (Λ e) η = 
      (halts eval-refl val-lam) , 
       lam-case e η
    all-HT (e₁ $ e₂) η with all-HT e₁ η
    ... | _ , HT₁ = HT₁ (ssubst _ e₂) (all-HT e₂ η)
    all-HT zero η = {!!} --halts eval-refl val-zero
    all-HT (suc e) η = {!!}
    all-HT (rec e e₀ es) η = {!!}

{-
  all-halt : ∀{A} → (e : TCExp A) → THalts e
  all-halt e with all-HT e emptyHTΓ
  ... | ht with (empty-subst-nop e)
  ... | eq = {!eq!}
-}
