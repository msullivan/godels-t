module Eq.Theory where

open import Prelude
open import T
open import DynTheory
open import SubstTheory
open import Contexts
open import Eq.Defs
open import Eq.KleeneTheory
open import Eq.ObsTheory
open import Eq.LogicalTheory

-- Theory about the interactions between the relationships between the equivs

-- Now that we have shown that logical equivalence is a consistent congruence,
-- it follows that it is contained in observational equivalence.
obs-contains-logical : ∀{Γ} {A} → OLogicalEq Γ A ⊆ ObservEq Γ A
obs-contains-logical = obs-is-coarsest OLogicalEq log-is-con-congruence

obs-contains-clogical : ∀{A} → (LogicalEq A) ⊆ (ObservEq [] A)
obs-contains-clogical leq = obs-contains-logical (closed-logical-imp-open leq)

-- Show that observational equivalence implies logical for closed terms.
obs-implies-closed-logical : ∀{A} {e e' : TCExp A} →
                             [] ⊢ e ≅ e' :: A →
                             e ~ e' :: A
obs-implies-closed-logical {nat} oeq = ObservEq.observe oeq ∘
obs-implies-closed-logical {A ⇒ B} {e} {e'} oeq = body
  where body : (e₁ e₁' : TExp [] A) → LogicalEq A e₁ e₁' → LogicalEq B (e $ e₁) (e' $ e₁')
        body e₁ e₁' leq with obs-contains-clogical leq
        ... | oeq' with obs-trans (obs-congruence oeq' (e e$ ∘)) (obs-congruence oeq (∘ $e e₁'))
        ... | oeq'' = obs-implies-closed-logical oeq''

obs-contains-logical-subst : ∀{Γ} → SubstRel LogicalEq Γ ⊆ SubstRel (ObservEq []) Γ
obs-contains-logical-subst η x = obs-contains-clogical (η x)

-- Since observational implies logical for closed terms and
-- respects substitution of observational equivalent terms,
-- logical equivalence contains observational.
logical-contains-obs : ∀{Γ} {A} → ObservEq Γ A ⊆ OLogicalEq Γ A
logical-contains-obs {Γ} {A} {e} {e'} oeq {γ} {γ'} η
  with substs-respect-obs oeq (obs-contains-logical-subst η)
... | coeq = obs-implies-closed-logical coeq


-- This is sort of silly. We need these lemmas to prove that logical
-- equivalence contains definitional.
nat-val-weakening : ∀{Γ} {n : TNat} → TVal n →
                    Σ[ e :: TExp Γ nat ] (∀{γ : TSubst Γ []} → n ≡ ssubst γ e)
nat-val-weakening val-zero = zero , (λ {γ} → Refl)
nat-val-weakening {Γ} {suc n} (val-suc v) with nat-val-weakening {Γ} v
... | e , subst-thing = (suc e) , (λ {γ} → resp suc subst-thing)

nat-logical-equiv-val : ∀{Γ} (γ : TSubst Γ []) (e : TExp Γ nat) →
                        Σ[ n :: TExp Γ nat ] ((ssubst γ n ~ ssubst γ e :: nat) × TVal (ssubst γ n))
nat-logical-equiv-val {Γ} γ e with kleene-refl {ssubst γ e}
... | kleeneq n val E1 E2 with nat-val-weakening {Γ} val
... | n' , is-val = n' , ((kleeneq n val (ID.coe1 (λ x → x ~>* n) is-val eval-refl) E1) ,
                          ID.coe1 TVal is-val val)

-- Logical equivalence contains definitional equivalence.
logical-contains-def : ∀{Γ} {A} → DefEq Γ A ⊆ OLogicalEq Γ A
logical-contains-def {y = e} def-refl η = ological-refl e η
logical-contains-def {x = e} {y = e'} (def-sym defeq) η =
  ological-sym {_} {_} {e'} {e} (logical-contains-def defeq) η
logical-contains-def {x = e} {y = e''} (def-trans {e' = e'} defeq1 defeq2) η
  with logical-contains-def defeq1 | logical-contains-def defeq2
... | leq1 | leq2 = ological-trans {_} {_} {e} {e'} {e''} leq1 leq2 η
logical-contains-def (def-cong defeq C) η = ological-is-congruence (logical-contains-def defeq) C η
logical-contains-def {Γ} {A} (def-beta {e = e} {e' = e'}) {γ} {γ'} η
  with step-beta {e = (ssubst (liftγ γ) e)} {e' = ssubst γ e'}
... | step with ological-refl e (extendLogicalEQΓ η (ological-refl e' η))

... | leq with subeq (compose-subst-noob γ' e') e ≡≡ subcomp γ' (singγ e') e
... | subeq-r with subcomp (singγ (ssubst γ e')) (liftγ γ) e
... | subeq-l with ID.coe2 (LogicalEq A) subeq-l subeq-r leq
... | leq' = logical-converse-evaluation-1 leq' (eval-step step)

logical-contains-def {Γ} {A} (def-rec-z {e0 = e0} {es = es}) {γ} {γ'} η with ological-refl e0 η
... | leq = logical-converse-evaluation-1 leq (eval-step step-rec-z)

-- This is super nasty. It has some code duplication when handling the congruence stuff.
-- And it also needs to deal with a bunch of nasty substitution crap.
-- The main source of nonstupid complication is that the step rule requires
-- n to be a value, and definitional equivalence does not.
logical-contains-def {Γ} {A} (def-rec-s {e = en} {e0 = e0} {es = es}) {γ} {γ'} η
  with nat-logical-equiv-val γ en
... | n , num-leq , is-val with ological-refl (rec en e0 es) η

... | full-leq with ological-is-congruence {e = ssubst γ n} {e' = ssubst γ en}
                    (closed-logical-imp-open num-leq) (rec1 ∘ (ssubst γ e0) (ssubst (liftγ γ) es))
                    (emptyLogicalEqΓ {γ = emptyγ} {γ' = emptyγ})
... | eq-with-γn-and-nasty-subst with ID.coe2 (LogicalEq A) (subid _) (subid _) eq-with-γn-and-nasty-subst
... | eq-with-γn with logical-trans eq-with-γn full-leq

... | leq-subrec with ological-refl (rec (suc en) e0 es) (logicalγ-refl {x = γ})
... | full-leq-s with ological-is-congruence {e = ssubst γ n} {e' = ssubst γ en}
                    (closed-logical-imp-open num-leq) (rec1 (suc ∘) (ssubst γ e0) (ssubst (liftγ γ) es))
                    (emptyLogicalEqΓ {γ = emptyγ} {γ' = emptyγ})
... | eq-with-sγn-and-nasty-subst with ID.coe2 (LogicalEq A) (subid _) (subid _) eq-with-sγn-and-nasty-subst
... | eq-with-sγn with logical-trans eq-with-sγn full-leq-s
... | leq-subrec-2 with ological-refl es (extendLogicalEQΓ η leq-subrec)

... | leq-unrolled with subeq (compose-subst-noob γ' (rec en e0 es)) es ≡≡
                        subcomp γ' (singγ (rec en e0 es)) es
... | subeq-l with subcomp (singγ (ssubst γ (rec n e0 es))) (liftγ γ) es
... | subeq-r with ID.coe2 (LogicalEq A) subeq-r subeq-l leq-unrolled
... | leq with step-rec-s {e = ssubst γ n} {e₀ = ssubst γ e0} {es = ssubst (liftγ γ) es} is-val
... | step with logical-converse-evaluation-1 leq (eval-step step)
... | leq-stepped = logical-trans (logical-sym leq-subrec-2) leq-stepped

-- Obvious corollary that observational equivalence contains definitional.
obs-contains-def : ∀{Γ} {A} → DefEq Γ A ⊆ ObservEq Γ A
obs-contains-def = obs-contains-logical o logical-contains-def


-- Proving this mostly out of spite, because one formulation
-- of my theory needed this for observational equivalence,
-- and there wasn't a good way to prove it other than appealing
-- to observational equivalence coinciding with logical, which
-- was what we were trying to prove.
weakened-equiv-log : ∀{Γ} {A} {e e' : TCExp A} →
                     e ~ e' :: A →
                     Γ ⊢ weaken-closed e ~ weaken-closed e' :: A
weakened-equiv-log {Γ} {A} {e} {e'} leq {γ} {γ'} η with subren γ closed-wkγ e | subren γ' closed-wkγ e'
... | eq1 | eq2 with closed-subst (γ o closed-wkγ) e | closed-subst (γ' o closed-wkγ) e'
... | eq1' | eq2' = ID.coe2 (LogicalEq A) (symm eq1' ≡≡ symm eq1) (symm eq2' ≡≡ symm eq2) leq

weakened-equiv-obs : ∀{Γ} {A} {e e' : TCExp A} →
                     [] ⊢ e ≅ e' :: A →
                     Γ ⊢ weaken-closed e ≅ weaken-closed e' :: A
weakened-equiv-obs {Γ} {A} {e} {e'} oeq = obs-contains-logical (weakened-equiv-log {Γ} {A} {e} {e'} (obs-implies-closed-logical oeq))


-- Some more stuff about renaming.
wkren1 : ∀{Γ A} → TRen Γ (A :: Γ)
wkren1 = (λ x → S x)

weaken1 : ∀{Γ A B} → TExp Γ B → TExp (A :: Γ) B
weaken1 e = ren wkren1 e

weakening-ignores : ∀{Γ A} (e₁ : TCExp A) (γ : TSubst Γ []) →
                    Sub≡ (λ x₁ → ssubst (singγ e₁) (ren wkren1 (γ x₁))) γ
weakening-ignores e₁ γ x = subren (singγ e₁) wkren1 (γ x)  ≡≡ subid (γ x)

-- Functional extensionality
function-ext-log : ∀{Γ A B} {e e' : TExp Γ (A ⇒ B)} →
                   (A :: Γ) ⊢ weaken1 e $ var Z ~ weaken1 e' $ var Z :: B →
                   Γ ⊢ e ~ e' :: A ⇒ B
function-ext-log {Γ} {A} {B} {e} {e'} leq {γ} {γ'} η e₁ e₁' leq'
  with leq (extendLogicalEQΓ η leq')
... | leq'' with subren (subComp (singγ e₁) (liftγ γ)) wkren1 e |
                 subren (subComp (singγ e₁') (liftγ γ')) wkren1 e'
... | eq1' | eq2' with eq1' ≡≡ subeq (weakening-ignores e₁ γ) e |
                       eq2' ≡≡ subeq (weakening-ignores e₁' γ') e'
... | eq1 | eq2 = ID.coe2 (LogicalEq B) (resp (λ x → x $ e₁) eq1) (resp (λ x → x $ e₁') eq2)  leq''

function-ext-obs : ∀{Γ A B} {e e' : TExp Γ (A ⇒ B)} →
                   (A :: Γ) ⊢ weaken1 e $ var Z ≅ weaken1 e' $ var Z :: B →
                   Γ ⊢ e ≅ e' :: A ⇒ B
function-ext-obs {e = e} {e' = e'} oeq = obs-contains-logical
                                         (function-ext-log {e = e} {e' = e'} (logical-contains-obs oeq))

-- Eta, essentially
-- The important part of the proof is the def-beta and the function-ext-obs,
-- but most of the actual work is fucking around with substitutions.
function-eta-obs : ∀{Γ A B} (e : TExp Γ (A ⇒ B)) →
                   Γ ⊢ e ≅ (Λ (weaken1 e $ var Z)) :: A ⇒ B
function-eta-obs {Γ} {A} {B} e with
  obs-sym (obs-contains-def (def-beta {e = ren (wk wkren1) (ren wkren1 e) $ var Z} {e' = var Z}))

... | beta-eq with (subren (singγ (var Z)) (wk wkren1) (weaken1 e)) ≡≡
                   (subren (λ x → singγ (var Z) (wk wkren1 x)) wkren1 e) ≡≡
                   symm (subren emptyγ wkren1 e) ≡≡
                   subid (weaken1 e)
... | eq2 with resp (λ x → x $ var Z) eq2
... | eq with ID.coe2 (ObservEq (A :: Γ) B) eq refl beta-eq
... | oeq = function-ext-obs oeq

obs-equiv-nat-val : (e : TNat) → Σ[ n :: TNat ] (TVal n × ([] ⊢ e ≅ n :: nat))
obs-equiv-nat-val e with ological-equiv-nat-val e
obs-equiv-nat-val e | n , val , eq = n , val , obs-contains-logical eq


-- OK, maybe we are trying this with numerals again. Argh.

t-numeral : ∀{Γ} → Nat → TExp Γ nat
t-numeral Z = zero
t-numeral (S n) = suc (t-numeral n)

numeral-val : ∀{Γ} → (n : Nat) → TVal {Γ} (t-numeral n)
numeral-val Z = val-zero
numeral-val (S n) = val-suc (numeral-val n)

val-numeral : ∀{Γ} {e : TExp Γ nat} → TVal e → Σ[ n :: Nat ] (e ≡ t-numeral n)
val-numeral val-zero = Z , Refl
val-numeral (val-suc v) with val-numeral v
... | n , eq = (S n) , (resp suc eq)


numeral-subst-dontcare : ∀{Γ Γ'} (n : Nat) (γ : TSubst Γ Γ') → ssubst γ (t-numeral n) ≡ t-numeral n
numeral-subst-dontcare Z γ = Refl
numeral-subst-dontcare (S n) γ = resp suc (numeral-subst-dontcare n γ)


--
obs-equiv-numeral : (e : TNat) → Σ[ n :: Nat ] ([] ⊢ e ≅ t-numeral n :: nat)
obs-equiv-numeral e with obs-equiv-nat-val e
obs-equiv-numeral e | en , val , oeq with val-numeral val
... | n , eq = n , (ID.coe1 (ObservEq [] nat e) eq oeq)


dropSubstRel : ∀(R : CRel) {Γ A} {γ γ' : TSubst (A :: Γ) []} →
               SubstRel R (A :: Γ) γ γ' →
               SubstRel R Γ (dropγ γ) (dropγ γ')
dropSubstRel R η n = η (S n)
dropLogicalEqΓ = dropSubstRel LogicalEq

-- Allow induction over nats, essentially
function-induction-log : ∀{Γ A} {e e' : TExp (nat :: Γ) A} →
                         ((n : Nat) → Γ ⊢ ssubst (singγ (t-numeral n)) e ~
                                          ssubst (singγ (t-numeral n)) e' :: A) →
                         (nat :: Γ) ⊢ e ~ e' :: A
function-induction-log {Γ} {A} {e} {e'} f {γ} {γ'} η
  with η Z | obs-equiv-numeral (γ Z)
... | n-eq | n , oeq-n with f n (dropLogicalEqΓ η)
... | butt with subcomp (dropγ γ) (singγ (t-numeral n)) e | subcomp (dropγ γ') (singγ (t-numeral n)) e'
... | lol1 | lol2 with subeq (compose-subst-noob (dropγ γ) (t-numeral n)) e |
                       subeq (compose-subst-noob (dropγ γ') (t-numeral n)) e'
... | lol1' | lol2' with ID.coe2 (LogicalEq A) (symm lol1 ≡≡ symm lol1') (symm lol2 ≡≡ symm lol2') butt
... | wtf with ID.coe2
               (λ x y → LogicalEq A
                        (ssubst (extendγ (dropγ γ) x) e)
                        (ssubst (extendγ (dropγ γ') y) e'))
               (numeral-subst-dontcare n (dropγ γ)) (numeral-subst-dontcare n (dropγ γ')) wtf
... | wtf' with ological-refl e (extendLogicalEQΓ (dropLogicalEqΓ (logicalγ-refl {x = γ})) (obs-consistent oeq-n))
... | leq-e with ID.coe2 (LogicalEq A) (symm (subeq (drop-fix γ) e)) Refl leq-e
... | leq-e' with ological-refl e' (extendLogicalEQΓ (dropLogicalEqΓ (logicalγ-refl {x = γ'}))
                                    (kleene-trans (kleene-sym n-eq) (obs-consistent oeq-n)))
... | leq-e2 with ID.coe2 (LogicalEq A) (symm (subeq (drop-fix γ') e')) Refl leq-e2
... | leq-e2' = logical-trans leq-e' (logical-trans wtf' (logical-sym leq-e2'))


function-induction-obs : ∀{Γ A} {e e' : TExp (nat :: Γ) A} →
                         ((n : Nat) → Γ ⊢ ssubst (singγ (t-numeral n)) e ≅
                                          ssubst (singγ (t-numeral n)) e' :: A) →
                         (nat :: Γ) ⊢ e ≅ e' :: A
function-induction-obs {Γ} {A} {e} {e'} f =
                           obs-contains-logical
                            (function-induction-log {Γ} {A} {e} {e'}
                             (λ n → logical-contains-obs (f n)))
