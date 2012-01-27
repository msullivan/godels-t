module DenotCommutes where

open import Prelude
open import T

---- incomplete proof that the denotational
---- semantics commute with the dynamics

postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                 (∀ a → f {a} ≡ g {a}) →
                 _≡_ { A = {a : A} → B a} f g

postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                (∀ a → f a ≡ g a) → f ≡ g


module DenotCommutes where
  ---- dynamic semantics commute with denotational semantics
  lift-nγ : ∀{Γ Γ'}K → TSubst Γ Γ' → TSubst (K ++ Γ) (K ++ Γ')
  lift-nγ [] γ = γ
  lift-nγ (A :: K) γ = liftγ (lift-nγ K γ)

  data MList : Ctx -> Set where
    [] : MList []
    _::_ : ∀{Γ A} → interp A → MList Γ → MList (A :: Γ)

  extend-nη : ∀{Γ K} → meaningη Γ → MList K → meaningη (K ++ Γ)
  extend-nη η [] = η
  extend-nη η (x :: xs) = extendη (extend-nη η xs) x


  sn-ren : ∀{Γ}K → TRen Γ (K ++ Γ)
  sn-ren [] = renId
  sn-ren (x :: xs) = renComp S (sn-ren xs)

  ren-sn : ∀{Γ A}K → TExp Γ A → TExp (K ++ Γ) A
  ren-sn K e = ren (sn-ren K) e


  meaning-wk : ∀{A Γ} (e : TExp Γ A) (η : meaningη Γ) (Γ' : Ctx) (xs : MList Γ') →
                meaning e η ≡
                meaning (ren-sn Γ' e) (extend-nη η xs)
  meaning-wk (var x) η [] [] = Refl
  meaning-wk (var x) η (A' :: Γ') (x' :: xs) = meaning-wk (var x) η Γ' xs
  meaning-wk (Λ e) η Γ' xs = {!!}
  meaning-wk (e₁ $ e₂) η Γ' xs = {!!}
  meaning-wk zero η Γ' xs = Refl
  meaning-wk (suc e) η Γ' xs = {!!}
  meaning-wk (rec e e₀ es) η Γ' xs = {!!}

{-
  meaning-wk {A ⇒ _} (Λ e) η x Γ' xs  = ext lemma
    where lemma : (a : interp A) → meaning e (extendη η a) ≡
                                   meaning (ren (wk S) e) (extendη (extendη η x) a)
          lemma a with meaning-wk e (extendη η a) x
          ... | butt = {!!}
  meaning-wk (e₁ $ e₂) η x Γ' xs  = resp2 (id _) (meaning-wk e₁ η x) (meaning-wk e₂ η x)
  meaning-wk zero η x Γ' xs  = Refl
  meaning-wk (suc e) η x Γ' xs  = {!!}
  meaning-wk (rec e e₀ es) η x Γ' xs  = {!!}
-}
  meaning-subst : ∀{A B}Γ (xs : MList Γ) (e' : TCExp B)(e : TExp (Γ ++ [ B ]) A) →
                  meaning e (extend-nη (extendη emptyη (cmeaning e')) xs) ≡
                  meaning (ssubst (lift-nγ Γ (singγ e')) e) (extend-nη emptyη xs)
  meaning-subst [] [] e' (var Z) = Refl
  meaning-subst [] [] e' (var (S ()))
  meaning-subst (C :: Γ) (x :: xs) e' (var Z) = Refl
  meaning-subst (C :: Γ) (x :: xs) e' (var (S n)) =
      meaning-subst Γ xs e' (var n) ≡≡ symm {!!}
--meaning-wk (lift-nγ Γ (singγ e') n) (extend-nη emptyη xs) x
  meaning-subst Γ xs e' (Λ e) =
      ext (λ x → meaning-subst (_ :: Γ) (x :: xs) e' e)
  meaning-subst Γ xs e' (e₁ $ e₂) =
      resp2 (id _) (meaning-subst Γ xs e' e₁) (meaning-subst Γ xs e' e₂)
  meaning-subst Γ xs e' zero = Refl
  meaning-subst Γ xs e' (suc e) = resp S (meaning-subst Γ xs e' e)
  meaning-subst Γ xs e' (rec e e₀ es) = {!!}

  meaning-subst' : ∀{A B}(e' : TCExp B)(e : TExp [ B ] A) →
                  meaning e (extendη emptyη (cmeaning e')) ≡
                  cmeaning (subst e' e)
  meaning-subst' = meaning-subst [] []

  meaning-steps : ∀{A}{e e' : TCExp A} → (e ~> e') → cmeaning e ≡ cmeaning e'
  meaning-steps {e = e₁ $ e₂} (step-app-l St) =
         resp (λ f → f (meaning e₂ emptyη)) (meaning-steps St)
  meaning-steps {e = e₁ $ e₂} (step-app-r St) =
         resp (λ x → meaning e₁ emptyη x) (meaning-steps St)
  meaning-steps {e = (Λ e₁) $ e₂} step-beta = meaning-subst' e₂ e₁
  meaning-steps (step-suc St) = resp S (meaning-steps St)
  meaning-steps {e = rec e e₀ es} (step-rec St) =
         resp (λ e' → NAT.fold (meaning e₀ emptyη)
                        (λ n x → meaning es (extendη emptyη x)) e')
              (meaning-steps St)
  meaning-steps step-rec-z = Refl
  meaning-steps {e = rec (suc e) e₀ es} step-rec-s = meaning-subst' (rec e e₀ es) es


open DenotCommutes public
