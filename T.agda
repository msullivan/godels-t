-- We use the strategy for representing substitutions and renamings presented in:
--  http://thread.gmane.org/gmane.comp.lang.agda/3259
-- It is kind of unpleasant. There are a lot of lemmas we need to prove,
-- and treating renaming and substitution completely seperately is ugly.
-- The first reply to the post linked above presents a refinement that
-- avoids these problems, but at the cost of moving weakening into
-- every substitution function, where we can't reason about it.

module T where

open import Prelude

-- We could avoid needing to do this, but it would be a pain in the
-- ass.  We would have to do a lot of passing around of proofs that
-- substitutions behave the same.  It's easier to just use postulated
-- extensional equivalence to convert those proofs into full
-- equality proofs.
postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                 (∀ a → f {a} ≡ g {a}) →
                 _≡_ { A = {a : A} → B a} f g

postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                (∀ a → f a ≡ g a) → f ≡ g


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
  ---- Generic stuff about substitutions and renamings
  -- Renamings
  TRen : Ctx → Ctx → Set
  TRen Γ Γ' = ∀ {A} → A ∈ Γ → A ∈ Γ'

  renext : ∀ {Γ Γ'}{f g : TRen Γ Γ'} → (∀ {A} x → f {A} x ≡ g {A} x) → _≡_ {A = TRen Γ Γ'} f g
  renext f = iext (λ _ → ext f)

  renId : ∀{Γ} → TRen Γ Γ
  renId = \ x -> x

  renComp : ∀{B Γ Δ} → TRen Γ Δ → TRen B Γ → TRen B Δ
  renComp f g = f o g

  wk : ∀{Γ Γ' A} → TRen Γ Γ' → TRen (A :: Γ) (A :: Γ')
  wk f Z = Z
  wk f (S n) = S (f n)

  ren : ∀{Γ Γ'} → TRen Γ Γ' → ∀ {A} → TExp Γ A → TExp Γ' A
  ren γ (var x) = var (γ x)
  ren γ (Λ e) = Λ (ren (wk γ) e)
  ren γ (e₁ $ e₂) = (ren γ e₁) $ (ren γ e₂)
  ren γ zero = zero
  ren γ (suc e) = suc (ren γ e)
  ren γ (rec e e₀ es) = rec (ren γ e) (ren γ e₀) (ren (wk γ) es)

  -- Some theorems about renamings
  wkid : ∀{Γ A C} (x : A ∈ C :: Γ) → wk renId x ≡ renId x
  wkid Z = Refl
  wkid (S n) = Refl

  renid : ∀{Γ A} (e : TExp Γ A) → ren renId e ≡ id _ e
  renid (var x) = Refl
  renid (Λ e) = resp Λ (resp (λ (f : TRen _ _) → ren f e) 
                              (renext wkid)
                        ≡≡ renid e)
  renid (e₁ $ e₂) = resp2 _$_ (renid e₁) (renid e₂)
  renid zero = Refl
  renid (suc e) = resp suc (renid e)
  renid (rec e e₀ es) = resp3 rec (renid e) (renid e₀)
                        (resp (λ (f : TRen _ _) → ren f es)
                              (renext wkid)
                          ≡≡ renid es)

  wkcomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {C A} (x : A ∈ (C :: B)) →
             wk (renComp f g) x ≡ (wk f o wk g) x
  wkcomp f g Z = Refl
  wkcomp f g (S n) = Refl

  rencomp : ∀ {B Γ Γ'}(f : TRen Γ Γ')(g : TRen B Γ) {A} (e : TExp B A) →
             ren (renComp f g) e ≡ (ren f o ren g) e
  rencomp f g (var x) = Refl
  rencomp f g (Λ e) = resp Λ (resp (λ (f : TRen _ _) → ren f e) 
                              (renext (wkcomp f g))
                              ≡≡ (rencomp (wk f) (wk g) e))
  rencomp f g (e₁ $ e₂) = resp2 _$_ (rencomp f g e₁) (rencomp f g e₂)
  rencomp f g zero = Refl
  rencomp f g (suc e) = resp suc (rencomp f g e)
  rencomp f g (rec e e₀ es) = resp3 rec (rencomp f g e) (rencomp f g e₀)
                              (resp (λ (f : TRen _ _) → ren f es) 
                               (renext (wkcomp f g))
                               ≡≡ (rencomp (wk f) (wk g) es))

  -- Substitutions
  TSubst : Ctx → Ctx → Set
  TSubst Γ Γ' = ∀ {A} → A ∈ Γ → TExp Γ' A

  subext : ∀ {Γ Γ'}{f g : TSubst Γ Γ'} → (∀ {A} x → f {A} x ≡ g {A} x) → _≡_ {A = TSubst Γ Γ'} f g
  subext f = iext (λ _ → ext f)

  emptyγ : ∀{Γ} → TSubst Γ Γ
  emptyγ = λ x → var x

  liftγ : ∀{Γ Γ' A} → TSubst Γ Γ' → TSubst (A :: Γ) (A :: Γ')
  liftγ γ Z = var Z
  liftγ γ (S n) = ren S (γ n)

  singγ : ∀{Γ A} → TExp Γ A → TSubst (A :: Γ) Γ
  singγ e Z = e
  singγ e (S n) = var n

  ssubst : ∀{Γ Γ' C} →
           (γ : TSubst Γ Γ') →
           (e : TExp Γ C) →
           TExp Γ' C
  ssubst γ (var x) = γ x
  ssubst γ (Λ e) = Λ (ssubst (liftγ γ) e)
  ssubst γ (e₁ $ e₂) = (ssubst γ e₁) $ (ssubst γ e₂)
  ssubst γ zero = zero
  ssubst γ (suc e) = suc (ssubst γ e)
  ssubst γ (rec e e₀ es) = rec (ssubst γ e) (ssubst γ e₀) (ssubst (liftγ γ) es)

  subComp : ∀{B Γ Γ'} → TSubst Γ Γ' → TSubst B Γ → TSubst B Γ'
  subComp f g = ssubst f o g

  extendγ : ∀{Γ Γ' A} → TSubst Γ Γ' → TExp Γ' A → TSubst (A :: Γ) Γ'
  extendγ γ e = subComp (singγ e) (liftγ γ)

  -- Theorems about renaming and substitution
  renwklift : ∀{K Γ Δ C}(f : TRen Γ Δ)(g : TSubst K Γ){A}(x : A ∈ (C :: K)) →
          (ren (wk f) o (liftγ g)) x ≡ liftγ (ren f o g) x
  renwklift f g Z = Refl
  renwklift f g (S n) = symm (rencomp (wk f) S (g n)) ≡≡ rencomp S f (g n)

  rensub : ∀{B Γ Δ}(f : TRen Γ Δ)(g : TSubst B Γ){A}(e : TExp B A) →
          (ren f o ssubst g) e ≡ ssubst (ren f o g) e
  rensub f g (var x) = Refl
  rensub f g (Λ e) = resp Λ ((rensub (wk f) (liftγ g) e) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f e)
                              (subext (renwklift f g)))
  rensub f g (e₁ $ e₂) = resp2 _$_ (rensub f g e₁) (rensub f g e₂)
  rensub f g zero = Refl
  rensub f g (suc e) = resp suc (rensub f g e)
  rensub f g (rec e e₀ es) = resp3 rec (rensub f g e) (rensub f g e₀)
                              ((rensub (wk f) (liftγ g) es) ≡≡ 
                               resp (λ (f : TSubst _ _) → ssubst f es)
                               (subext (renwklift f g)))

  liftwk : ∀{K Γ Δ C}(f : TSubst Γ Δ)(g : TRen K Γ){A}(x : A ∈ (C :: K)) →
                     (liftγ f o wk g) x ≡ liftγ (f o g) x
  liftwk f g Z = Refl
  liftwk f g (S n) = Refl

  subren : ∀{B Γ Δ}(f : TSubst Γ Δ)(g : TRen B Γ){A}(e : TExp B A) →
          (ssubst f o ren g) e ≡ ssubst (f o g) e
  subren f g (var x) = Refl
  subren f g (Λ e) = resp Λ ((subren (liftγ f) (wk g) e) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f e)
                              (subext (liftwk f g)))
  subren f g (e₁ $ e₂) = resp2 _$_ (subren f g e₁) (subren f g e₂)
  subren f g zero = Refl
  subren f g (suc e) = resp suc (subren f g e)
  subren f g (rec e e₀ es) = resp3 rec (subren f g e) (subren f g e₀)
                             ((subren (liftγ f) (wk g) es) ≡≡ 
                              resp (λ (f : TSubst _ _) → ssubst f es)
                              (subext (liftwk f g)))

  -- first monad law, the second holds definitionally
  liftid : ∀{Γ A C} (x : A ∈ C :: Γ) → liftγ emptyγ x ≡ emptyγ x
  liftid Z = Refl
  liftid (S n) = Refl

  subid : ∀{Γ}{A} (e : TExp Γ A) → ssubst emptyγ e ≡ id _ e
  subid (var x) = Refl
  subid (Λ e) = resp Λ (resp (λ (f : TSubst _ _) → ssubst f e) (subext liftid) ≡≡ subid e)
  subid (e₁ $ e₂) = resp2 _$_ (subid e₁) (subid e₂)
  subid zero = Refl
  subid (suc e) = resp suc (subid e)
  subid (rec e e₀ es) = resp3 rec (subid e) (subid e₀)
                        (resp (λ (f : TSubst _ _) → ssubst f es) (subext liftid) ≡≡ subid es)


  -- third monad law
  liftcomp : ∀ {B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ) {C A} (x : A ∈ (C :: B)) →
             liftγ (subComp f g) x ≡ (ssubst (liftγ f) o liftγ g) x
  liftcomp f g Z = Refl
  liftcomp f g (S n) = rensub S f (g n) ≡≡ symm (subren (liftγ f) S (g n))

  subcomp : ∀{B Γ Γ'}(f : TSubst Γ Γ')(g : TSubst B Γ){A}(t : TExp B A) →
         ssubst (subComp f g) t ≡ (ssubst f o ssubst g) t
  subcomp f g (var x) = Refl
  subcomp f g (Λ e) = resp Λ ((resp (λ (f : TSubst _ _) → ssubst f e) 
                              (subext (liftcomp f g)))
                              ≡≡ (subcomp (liftγ f) (liftγ g) e))
  subcomp f g (e₁ $ e₂) = resp2 _$_ (subcomp f g e₁) (subcomp f g e₂)
  subcomp f g zero = Refl
  subcomp f g (suc e) = resp suc (subcomp f g e)
  subcomp f g (rec e e₀ es) = resp3 rec (subcomp f g e) (subcomp f g e₀)
                              ((resp (λ (f : TSubst _ _) → ssubst f es) 
                               (subext (liftcomp f g)))
                               ≡≡ (subcomp (liftγ f) (liftγ g) es))

  -- substituting one thing in a closed term
  subst : ∀{A C} → (e' : TCExp A) → (e : TExp (A :: []) C) → TCExp C
  subst e' e = ssubst (singγ e') e


  combine-subst-noob : ∀ {Γ A C} → (γ : TSubst Γ []) →
                    (e : TExp (A :: Γ) C) →
                    (e' : TCExp A) →
                    ssubst (extendγ γ e') e ≡
                    ssubst (singγ e') (ssubst (liftγ γ) e)
  combine-subst-noob γ e e' = subcomp (singγ e') (liftγ γ) e

  extend-nofail-s : ∀{Γ Γ' A B} → (γ : TSubst Γ Γ') → (e : TExp Γ' A) → (n : B ∈ Γ) →
                    (extendγ γ e) (S n) ≡ γ n
  extend-nofail-s γ e n = subren (singγ e) S (γ n) ≡≡ subid (γ n)


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
  HTΓ Γ γ = ∀{A} (x : A ∈ Γ) -> HT A (γ x)

  emptyHTΓ : ∀{η : TSubst [] []} -> HTΓ [] η
  emptyHTΓ ()

  extendHTΓ : ∀{Γ A} {e : TCExp A} {γ : TSubst Γ []} ->
              HTΓ Γ γ -> HT A e -> HTΓ (A :: Γ) (extendγ γ e)
  extendHTΓ η ht Z = ht
  extendHTΓ {_} {_} {e} {γ} η ht {B} (S n) = 
             ID.coe1 (λ x → HT B x) (symm (extend-nofail-s γ e n)) (η n)

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
    where lam-case : (e' : TCExp A) → HT A e' → HT B (Λ (ssubst (liftγ γ) e) $ e')
          lam-case e' ht' with all-HT {γ = extendγ γ e'} e (extendHTΓ η ht')
          ... | ht with eval-step (step-beta {e = (ssubst (liftγ γ) e)})
          ... | steps-full with combine-subst-noob γ e e'
          ... | eq = head-expansion steps-full (ID.coe1 (HT B) eq ht)

  all-HT {Γ} {A} {γ} (rec e e₀ es) η = inner (all-HT e η)
    where inner : {e : TNat} → HTω e → HT A (rec e (ssubst γ e₀) (ssubst (liftγ γ) es))
          inner (HT-z E) with eval-trans (eval-rec {es = (ssubst (liftγ γ) es)} E)
                              (eval-step step-rec-z)
          ... | steps-full = head-expansion steps-full (all-HT e₀ η)
          inner {e} (HT-s E ht') with all-HT {γ = extendγ γ _} es (extendHTΓ η (inner ht'))
          ... | ht with eval-trans (eval-rec {e₀ = (ssubst γ e₀)} E) (eval-step step-rec-s)
          ... | steps-full with combine-subst-noob γ es _
          ... | eq = head-expansion steps-full (ID.coe1 (HT _) eq ht)


  all-halt : ∀{A} → (e : TCExp A) → THalts e
  all-halt {A} e = HT-halts e (ID.coe1 (HT A) (subid e) (all-HT e (emptyHTΓ {emptyγ})))

  ---- some example programs
  -- boy, de bruijn indexes are unreadable
  bs-subst : ∀{Γ} → TRen [] Γ
  bs-subst ()

  w : ∀{Γ B} → TCExp B → TExp Γ B
  w e = ren bs-subst e

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
  t-iterate = Λ (Λ (rec (var (S Z)) (w t-id)
                     (w t-compose $ var (S Z) $ var Z)))
  t-ack : TCExp (nat ⇒ nat ⇒ nat)
  t-ack = Λ (rec (var Z) (Λ (suc (var Z)))
              (Λ (w t-iterate $ var Z $ var (S Z) $ (var (S Z) $ w one))))


open GÖDEL-T public
