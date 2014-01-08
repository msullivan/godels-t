module Examples where

open import Prelude
open import T

---- some example programs
-- boy, de bruijn indexes are unreadable
bs-subst : ∀{Γ} → TRen [] Γ
bs-subst ()

w : ∀{Γ B} → TCExp B → TExp Γ B
w e = ren bsRename e

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
ack-test : TNat
ack-test = t-ack $ two $ two
plus-test : TNat
plus-test = t-plus $ two $ two
