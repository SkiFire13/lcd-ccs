{-# OPTIONS --safe --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.context (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.congruence C N penv renaming (cong to ~-cong)
open import bisimilarity.strong.properties C N penv using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv using (~→≈) renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

-- Observational congruence defined as the contextual closure over weak bisimilarity
_̂≈_ : Proc → Proc → Set₁
_̂≈_ p q = (C[] : Context) → subst C[] p ≈ subst C[] q

-- Prove that ̂≈ is an equivalence

reflexive : ∀ {p} → p ̂≈ p
reflexive = λ _ → ≈-refl

sym : ∀ {p q} → p ̂≈ q → q ̂≈ p
sym C[p]≈C[q] = λ C[] → ≈-sym (C[p]≈C[q] C[])

trans : ∀ {p q s} → p ̂≈ q → q ̂≈ s → p ̂≈ s
trans C[p]≈C[q] C[q]≈C[s] = λ C[] → ≈-trans (C[p]≈C[q] C[]) (C[q]≈C[s] C[])

-- Prove that ̂≈ implies ≈,
̂≈→≈ : ∀ {p q} → p ̂≈ q → p ≈ q
̂≈→≈ C[p]≈C[q] = C[p]≈C[q] hole

-- Lemma to help prove `cong`
-- Prove that `compose` is the same as composing `subst` under strong bisimilarity
ss~sc : ∀ {C₁[] C₂[] p} → subst C₁[] (subst C₂[] p) ~ subst (compose C₁[] C₂[]) p
ss~sc {chan a C[]} = ~-cong {chan a hole} (ss~sc {C[]})
ss~sc {par C[] p} = ~-cong {par hole p} (ss~sc {C[]})
p⇒q (ss~sc {indet C[] _}) (indet s t) with s
... | left  = let q' , t' , p'~q' = ss~sc {C[]} .p⇒q t in q' , indet left t' , p'~q'
... | right = _ , indet right t , ~-refl
q⇒p (ss~sc {indet C[] _}) (indet s t) with s
... | left  = let q' , t' , p'~q' = ss~sc {C[]} .q⇒p t in q' , indet left t' , p'~q'
... | right = _ , indet right t , ~-refl
ss~sc {rename f C[]} = ~-cong {rename f hole} (ss~sc {C[]})
ss~sc {hide f C[]} = ~-cong {hide f hole} (ss~sc {C[]})
ss~sc {hole} = ~-refl

-- Prove that ̂≈ is a congruence
cong : Cong _̂≈_
cong {C[]} {p} {q} C[p]≈C[q] = λ C'[] →
  let t₁ = ~→≈ (ss~sc {C'[]} {C[]} {p})
      t₂ = C[p]≈C[q] (compose C'[] C[])
      t₃ = ~→≈ (ss~sc {C'[]} {C[]} {q})
  in  ≈-trans (≈-trans t₁ t₂) (≈-sym t₃)

-- Prove that any subset of weak bisimilarity that is also a congruence imply observational congruence
≈-cong→̂≈ : ∀ {_≈ₓ_ p q} → (∀ {p' q'} → p' ≈ₓ q' → p' ≈ q') → Cong _≈ₓ_ → p ≈ₓ q → p ̂≈ q
≈-cong→̂≈ ≈ₓ→≈ Cong≈ₓ p≈ₓq = λ _ → ≈ₓ→≈ (Cong≈ₓ p≈ₓq)
