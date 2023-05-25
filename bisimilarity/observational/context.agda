{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.observational.context (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.cong C N penv
open import bisimilarity.context C N penv
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.congruence C N penv renaming (cong to ~-cong)
open import bisimilarity.strong.properties C N penv using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv using (~→≈) renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

-- Observational congruence defined as a closure over weak bisimilarity in contexts
record _̂≈_ (p : Proc) (q : Proc) : Set₁ where
  constructor obs-c
  field
    closure : (C[] : Context) → (subst C[] p) ≈ (subst C[] q)
open _̂≈_ public

-- Prove that ̂≈ is an equivalence
reflexive : ∀ {p} → p ̂≈ p
reflexive = obs-c λ _ → ≈-refl

sym : ∀ {p q} → p ̂≈ q → q ̂≈ p
sym (obs-c C[p]≈C[q]) = obs-c λ C[] → ≈-sym (C[p]≈C[q] C[])

trans : ∀ {p q s} → p ̂≈ q → q ̂≈ s → p ̂≈ s
trans (obs-c C[p]≈C[q]) (obs-c C[q]≈C[s]) = obs-c λ C[] → ≈-trans (C[p]≈C[q] C[]) (C[q]≈C[s] C[])

-- Prove that ̂≈ implies ≈, even though it is pretty obvious
̂≈→≈ : ∀ {p q} → p ̂≈ q → p ≈ q
̂≈→≈ (obs-c C[p]≈C[q]) = C[p]≈C[q] replace

-- Prove that ̂≈ is a congruence
cong : Cong _̂≈_
cong {C[]} {p} {q} (obs-c C[p]≈C[q]) = obs-c λ C'[] →
  let t1 = ~→≈ (ss~sc {C'[]} {C[]} {p})
      t2 = C[p]≈C[q] (compose C'[] C[])
      t3 = ~→≈ (ss~sc {C'[]} {C[]} {q})
  in ≈-trans (≈-trans t1 t2) (≈-sym t3)

≈-cong→̂≈ : ∀ {_≈ₓ_ p q} → (∀ {p' q'} → p' ≈ₓ q' → p' ≈ q') → Cong _≈ₓ_ → p ≈ₓ q → p ̂≈ q
≈-cong→̂≈ {_≈ₓ_} ≈ₓ→≈ Cong≈ₓ p≈ₓq = obs-c λ _ → ≈ₓ→≈ (Cong≈ₓ p≈ₓq)
