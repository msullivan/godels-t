module ReasoningEx where

open import Prelude
open import T
open import Contexts
open import Eq
open import Eq.Theory
open import Eq.ObsTheory

---- some example programs
-- boy, de bruijn indexes are unreadable
w = weaken-closed

plus-rec : ∀{Γ} → TExp Γ nat → TExp Γ nat → TExp Γ nat
plus-rec n m = rec n m (suc (var Z))

t-plus1 : TCExp (nat ⇒ nat ⇒ nat)
t-plus1 = Λ (Λ (plus-rec (var Z) (var (S Z))))
t-plus2 : TCExp (nat ⇒ nat ⇒ nat)
t-plus2 = Λ (Λ (plus-rec (var (S Z)) (var Z)))

plus-adds : ∀{Γ} → (n : Nat) (m : Nat) →
            Γ ⊢ plus-rec (t-numeral n) (t-numeral m) ≅ t-numeral (n +n m) :: nat
plus-adds Z m = obs-contains-def def-rec-z
plus-adds {Γ} (S n) m with
  (def-rec-s {Γ} {e = (t-numeral n)} {e0 = t-numeral m} {es = suc (var Z)})
-- If I don't name the def eq thing above and use it directly, agda uses all my core.
... | bullshit-workaround with obs-contains-def bullshit-workaround
... | step-eq with obs-congruence (plus-adds {Γ} n m) (suc ∘)
... | reccase = obs-trans step-eq reccase


help : (n : Nat) → ObservEq (nat :: []) nat
                   (rec (t-numeral n) (var Z) (suc (var Z)))
                   (rec (var Z) (t-numeral n) (suc (var Z)))
help n = {!!}

plus-commutes : [] ⊢ t-plus1 ≅ t-plus2 :: nat ⇒ nat ⇒ nat
plus-commutes with
  def-cong (def-beta {e = Λ (plus-rec (var Z) (var (S Z)))} {e' = var (S Z)}) (∘ $e var Z) |
  def-cong (def-beta {e = Λ (plus-rec (var (S Z)) (var Z))} {e' = var (S Z)}) (∘ $e var Z)
... | beq1 | beq2 with def-beta {e = plus-rec (var Z) (var (S (S Z)))} {e' = var Z} |
                       def-beta {e = plus-rec (var (S (S Z))) (var Z)} {e' = var Z}
... | beq1' | beq2' with obs-contains-def (def-trans beq1 beq1') | obs-contains-def (def-trans beq2 beq2')
... | oeq1 | oeq2 with function-induction-obs help
... | main-eq with obs-trans oeq1 (obs-trans main-eq (obs-sym oeq2))
... | lol = function-ext-obs (function-ext-obs lol)
