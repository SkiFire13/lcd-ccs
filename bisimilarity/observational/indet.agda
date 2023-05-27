{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Base

import ccs.proc

module bisimilarity.observational.indet (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.congruence C N penv renaming (cong to ~-cong)
open import bisimilarity.strong.properties C N penv using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.congruence C N penv
open import bisimilarity.weak.properties C N penv renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

-- Observational congruence defined as a closure over weak bisimilarity in contexts
record _≈ᵢ_ (p : Proc) (q : Proc) : Set₁ where
  constructor obs-i
  field
    closure : (r : Proc) → p + r ≈ q + r
open _≈ᵢ_ public

-- Prove that ≈ᵢ is an equivalence

reflexive : ∀ {p} → p ≈ᵢ p
reflexive = obs-i λ _ → ≈-refl

sym : ∀ {p q} → p ≈ᵢ q → q ≈ᵢ p
sym (obs-i p+r≈q+r) = obs-i λ r → ≈-sym (p+r≈q+r r)

trans : ∀ {p q s} → p ≈ᵢ q → q ≈ᵢ s → p ≈ᵢ s
trans (obs-i p+r≈q+r) (obs-i q+r≈s+r) = obs-i λ r → ≈-trans (p+r≈q+r r) (q+r≈s+r r)

-- Prove that ≈ᵢ implies ≈, even though it is pretty obvious

p≈p+d : ∀ {p} → p ≈ p + ccs.deadlock
p⇒q (p≈p+d) t = _ , trans→weak (indet left t) , ≈-refl
q⇒p (p≈p+d) (indet left t) = _ , trans→weak t , ≈-refl
q⇒p (p≈p+d) (indet right (indet () _))

≈ᵢ→≈ : ∀ {p q} → p ≈ᵢ q → p ≈ q
≈ᵢ→≈ (obs-i p+r≈q+r) = ≈-trans (≈-trans p≈p+d (p+r≈q+r ccs.deadlock)) (≈-sym p≈p+d)

-- Prove that ≈ᵢ is a congruence

cong : Cong _≈ᵢ_
p⇒q (closure (cong p≈ᵢq) r) (indet {q = r'} right t) =
  r' , trans→weak (indet right t) , ≈-refl
p⇒q (closure (cong {chan c C[]} {q = q} p≈ᵢq) r) (indet left chan) =
  subst C[] q , trans→weak (indet left chan) , ≈ᵢ→≈ (cong p≈ᵢq)
p⇒q (closure (cong {par-L C[] pc} {q = q} p≈ᵢq) r) (indet left t) with t
... | par-L tl = {!   !}
... | par-R {p' = pc'} tr =
  par (subst C[] q) pc' , trans→weak (indet left (par-R tr)) , par-respects-≈ (≈ᵢ→≈ (cong {C[]} p≈ᵢq)) ≈-refl
... | par-B tl tr = {!   !}
p⇒q (closure (cong {par-R pc C[]} p≈ᵢq) r) (indet left t) = {!   !}
p⇒q (closure (cong {indet C[] pc} p≈ᵢq) r) t =
  ≈-trans (≈-trans helper (cong p≈ᵢq .closure (pc + r))) (≈-sym helper) .p⇒q t
  where
  helper : ∀ {p₁ p₂ p₃} → (p₁ + p₂) + p₃ ≈ p₁ + (p₂ + p₃)
  p⇒q helper (indet left (indet left t)) = _ , trans→weak (indet left t) , ≈-refl
  p⇒q helper (indet left (indet right t)) = _ , trans→weak (indet right (indet left t)), ≈-refl
  p⇒q helper (indet right t) = _ , trans→weak (indet right (indet right t)) , ≈-refl
  q⇒p helper (indet left t) = _ , trans→weak (indet left (indet left t)) , ≈-refl
  q⇒p helper (indet right (indet left t)) = _ , trans→weak (indet left (indet right t)) , ≈-refl
  q⇒p helper (indet right (indet right t)) = _ , trans→weak (indet right t), ≈-refl
p⇒q (closure (cong {rename f C[]} p≈ᵢq) r) (indet left t) = {!   !}
p⇒q (closure (cong {hide f C[]} p≈ᵢq) r) (indet left (hide z t)) = {!   !}
p⇒q (closure (cong {hole} p≈ᵢq) r) (indet left t) = p≈ᵢq .closure r .p⇒q (indet left t)
q⇒p (closure (cong p≈ᵢq) r) = cong (sym p≈ᵢq) .closure r .p⇒q
