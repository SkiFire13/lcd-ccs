{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.context-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.observational.context C N penv renaming (sym to ̂≈-sym)
open import bisimilarity.observational.trans C N penv renaming (cong to ≈ₒ-cong)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv renaming (sym to ≈-sym; trans to ≈-trans)

-- Prove that observational congruence defined by limiting self tau transitions
-- implies observational congruence defined as closure of bisimilarity over contexts. 
≈ₒ→̂≈ : ∀ {p q} → p ≈ₒ q → p ̂≈ q
≈ₒ→̂≈ p≈ₒq = ≈-cong→̂≈ ≈ₒ→≈ ≈ₒ-cong p≈ₒq

-- (Try to) prove that observational congruence defined as closure of bisimilarity over contexts
-- implies observational congruence defined by limiting self tau transitions.
-- The exercise only requires ≈ₒ→̂≈, with ̂≈→≈ₒ as an optional part because the given
-- hole is supposedly very difficult to fill (both in Agda and on paper)
̂≈→≈ₒ : (c : C) → ∀ {p q} → p ̂≈ q → p ≈ₒ q
p⇒q (̂≈→≈ₒ c (C[p]≈C[q])) {a = send _} t with C[p]≈C[q] Ctx .p⇒q (indet left t)
  where Ctx = indet hole ccs.deadlock
... | q' , send self (indet left tq) s₂ , p'≈q' = q' , obs-o self tq s₂ , p'≈q'
... | _ , send self (indet right (indet () _)) _ , _
... | q' , send (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs-o (cons tq s₁) tq' s₂ , p'≈q'
... | _ , send (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c (C[p]≈C[q])) {a = recv _} t with C[p]≈C[q] Ctx .p⇒q (indet left t)
  where Ctx = indet hole ccs.deadlock
... | q' , recv self (indet left tq) s₂ , p'≈q' = q' , obs-o self tq s₂ , p'≈q'
... | _ , recv self (indet right (indet () _)) _ , _
... | q' , recv (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs-o (cons tq s₁) tq' s₂ , p'≈q'
... | _ , recv (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c (C[p]≈C[q])) {a = tau} t = {!   !}
q⇒p (̂≈→≈ₒ c oc) = ̂≈→≈ₒ c (̂≈-sym oc) .p⇒q
