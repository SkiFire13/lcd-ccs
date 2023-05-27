{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.context-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.observational.context C N penv renaming (sym to ̂≈-sym)
open import bisimilarity.observational.trans C N penv renaming (cong to ≈ₒ-cong)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open import bisimilarity.weak.congruence C N penv

-- Prove that observational congruence defined by limiting self τ transitions
-- implies observational congruence defined as the contextual closure of weak bisimilarity.
≈ₒ→̂≈ : ∀ {p q} → p ≈ₒ q → p ̂≈ q
≈ₒ→̂≈ p≈ₒq = ≈-cong→̂≈ ≈ₒ→≈ ≈ₒ-cong p≈ₒq

-- (Try to) prove that observational congruence defined as the contextual closure of weak
-- bisimilarity implies observational congruence defined by limiting self τ transitions,
-- assuming C is inhabited.
-- The exercise only requires ≈ₒ→̂≈, with ̂≈→≈ₒ as an optional part because the given
-- hole is supposedly very difficult to fill (both in Agda and on paper).
̂≈→≈ₒ : C → ∀ {p q} → p ̂≈ q → p ≈ₒ q
p⇒q (̂≈→≈ₒ c C[p]≈C[q]) {a = send _} t with C[p]≈C[q] C[] .p⇒q (indet left t)
  where C[] = indet hole ccs.deadlock
... | q' , send self (indet left tq) s₂ , p'≈q' = q' , obs-o self tq s₂ , p'≈q'
... | _ , send self (indet right (indet () _)) _ , _
... | q' , send (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs-o (cons tq s₁) tq' s₂ , p'≈q'
... | _ , send (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c C[p]≈C[q]) {a = recv _} t with C[p]≈C[q] C[] .p⇒q (indet left t)
  where C[] = indet hole ccs.deadlock
... | q' , recv self (indet left tq) s₂ , p'≈q' = q' , obs-o self tq s₂ , p'≈q'
... | _ , recv self (indet right (indet () _)) _ , _
... | q' , recv (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs-o (cons tq s₁) tq' s₂ , p'≈q'
... | _ , recv (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c C[p]≈C[q]) {a = τ} t = {!   !}
q⇒p (̂≈→≈ₒ c C[p]≈C[q]) = ̂≈→≈ₒ c (̂≈-sym C[p]≈C[q]) .p⇒q

-- Prove that the assumption that C is inhabited is required for the previous theorem.
¬C→¬̂≈→≈ₒ : ¬ C → ¬ ∀ {p q} → p ̂≈ q → p ≈ₒ q
¬C→¬̂≈→≈ₒ ¬C ̂≈→≈ₒ with ̂≈→≈ₒ C[τd]≈C[d] .p⇒q chan
  where
  C[τd]≈C[d] : chan τ ccs.deadlock ̂≈ ccs.deadlock
  C[τd]≈C[d] = λ _ → ¬C→≈-always-true ¬C
... | _ , obs-o self (indet () _) _ , _
... | _ , obs-o (cons (indet () _) _) _ _ , _
