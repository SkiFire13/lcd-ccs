{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.context {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.congruence {C} {N} {penv} renaming (cong to ~-cong)
open import bisimilarity.strong.properties {C} {N} {penv} using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} using (~-to-≈) renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

-- Observational congruence defined as a closure over weak bisimilarity in contexts
record _̂≈_ (p : Proc) (q : Proc) : Set₁ where
  constructor obs-c
  field
    closure : (C[] : Context) -> (subst C[] p) ≈ (subst C[] q)
open _̂≈_ public

-- Prove that ̂≈ is an equivalence
reflexive : forall {p} -> p ̂≈ p
reflexive = obs-c \ _ -> ≈-refl

sym : forall {p q} -> p ̂≈ q -> q ̂≈ p
sym (obs-c C[p]≈C[q]) = obs-c \ C[] -> ≈-sym (C[p]≈C[q] C[])

trans : forall {p q s} -> p ̂≈ q -> q ̂≈ s -> p ̂≈ s
trans (obs-c C[p]≈C[q]) (obs-c C[q]≈C[s]) = obs-c \ C[] -> ≈-trans (C[p]≈C[q] C[]) (C[q]≈C[s] C[])

-- Prove that ̂≈ implies ≈, even though it is pretty obvious
̂≈-to-≈ : forall {p q} -> p ̂≈ q -> p ≈ q
̂≈-to-≈ (obs-c C[p]≈C[q]) = C[p]≈C[q] replace

-- Prove that ̂≈ is a congruence
cong : forall {C[] p q} -> p ̂≈ q -> (subst C[] p) ̂≈ (subst C[] q)
cong {C[]} {p} {q} (obs-c C[p]≈C[q]) = obs-c \ C'[] ->
  let t1 = ~-to-≈ (ss~sc {C'[]} {C[]} {p})
      t2 = C[p]≈C[q] (compose C'[] C[])
      t3 = ~-to-≈ (ss~sc {C'[]} {C[]} {q})
  in ≈-trans (≈-trans t1 t2) (≈-sym t3)
